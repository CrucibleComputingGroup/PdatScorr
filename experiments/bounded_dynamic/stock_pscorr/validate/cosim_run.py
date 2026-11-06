#!/usr/bin/env python3
"""Validate a Pscorr run by co-simulating its AIG before and after ABC.

1. Re-run the run's own Yosys script with `-map` added to `write_aiger` and check
   that the regenerated AIGER is byte-identical to the recorded one; the map names
   every primary input and output.
2. Build the stimulus spec: reset in cycle 0 (rare re-resets later), instruction
   words drawn from the allowed (mask, value) patterns of the generated CRISP
   assumptions, and, for channels with timing declarations, grants tied high and
   responses 1..N cycles after acceptance (per tag, or in order).
3. Run aigcosim (bit-parallel, 64 traces per round) on the recorded pre-ABC AIG and
   a post-ABC AIG made by the run's own ABC command, and record the result.

The post-ABC AIG is regenerated rather than read from the run because the stock
command writes it after `rewrite -l; balance -l`, which is what is compared here too.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CSIM = HERE / "aigcosim.c"


def sha(p: Path) -> str:
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


# CVA6 cv32a60x AXI ports are packed structs; yosys-slang flattens them to vectors, so
# members are located by offset (first member at the MSB). Widths: noc_resp_i 146,
# noc_req_o 374 (ID 4, address 64, data 64, user 32), checked against the map.
CVA6_RESP = {"r.user": (0, 32), "r.last": (32, 1), "r.resp": (33, 2), "r.data": (35, 64), "r.id": (99, 4),
             "r_valid": (103, 1), "b.user": (104, 32), "b.resp": (136, 2), "b.id": (138, 4), "b_valid": (142, 1),
             "w_ready": (143, 1), "ar_ready": (144, 1), "aw_ready": (145, 1)}
CVA6_REQ = {"r_ready": (0, 1), "ar_valid": (1, 1), "ar.id": (127, 4), "b_ready": (131, 1), "w_valid": (132, 1),
            "aw_valid": (238, 1), "aw.id": (370, 4)}
CVA6_ICACHE_DATA = "gen_cache_hpd.i_cache_subsystem.i_cva6_icache.gen_sram[{}].data_sram.rdata_o"


def aligned(pats):
    """Stimulus refinement: keep control-flow targets 4-byte aligned.

    Branch and JAL offsets get imm[1] = 0 and JALR is restricted to rs1 = x0 with
    imm[1:0] = 0. Every resulting word still satisfies its (mask, value) pattern, so
    the stimulus still satisfies the ISA assumptions; it only avoids fetching a word
    split across two instructions on a core with compressed-instruction support.
    """
    out = []
    for m, v in pats:
        m, v = int(m, 16), int(v, 16)
        op = v & 0x7F
        extra = {0x63: 1 << 8, 0x6F: 1 << 21, 0x67: (0x1F << 15) | (0x3 << 20)}.get(op, 0) if m & 0x7F == 0x7F else 0
        out.append((f"{m | extra:08x}", f"{v & ~extra:08x}"))
    return out


def cva6_spec(ins, outs, isa_patterns, channels):
    width = lambda d, n: sum(1 for (name, _b) in d if name == n)
    # The map omits constant output bits, so only the input width is checked; every
    # request bit used below must be present (a missing key raises).
    assert width(ins, "noc_resp_i") == 146, "unexpected AXI response struct width"
    assert max(b for (n, b) in outs if n == "noc_req_o") <= 373, "unexpected AXI request struct width"
    ri = lambda m, k=0: ins[("noc_resp_i", CVA6_RESP[m][0] + k)]
    ro = lambda m, k=0: outs[("noc_req_o", CVA6_REQ[m][0] + k)]
    spec = []
    lanes = [[ins[(CVA6_ICACHE_DATA.format(w), 32 * l + b)] for b in range(32)] for w in (0, 1) for l in range(4)]
    lanes += [[ri("r.data", 32 * l + b) for b in range(32)] for l in range(2)]
    spec += ["word " + " ".join(map(str, lane)) for lane in lanes]
    spec += [f"pattern {m} {v}" for m, v in isa_patterns]
    for item in channels:
        name, lat = item.split("=")
        if name == "rd":
            spec.append(f"const1 {ri('ar_ready')}")
            spec.append(" ".join(map(str, ["tagged", lat, ro("ar_valid"), ro("r_ready"), ri("r_valid"), ri("r.last"), 4]
                                     + [ro("ar.id", b) for b in range(4)] + [ri("r.id", b) for b in range(4)])))
        elif name == "wr":
            spec.append(f"const1 {ri('aw_ready')}")
            spec.append(" ".join(map(str, ["tagged", lat, ro("aw_valid"), ro("b_ready"), ri("b_valid"), -1, 4]
                                     + [ro("aw.id", b) for b in range(4)] + [ri("b.id", b) for b in range(4)])))
        elif name == "wdata":
            spec.append(f"const1 {ri('w_ready')}")
        else:
            raise SystemExit(f"unknown CVA6 channel {name}")
    return spec


def parse_map(path: Path):
    ins, outs = {}, {}
    for line in path.read_text().splitlines():
        f = line.split()
        if f and f[0] in ("input", "output"):
            (ins if f[0] == "input" else outs)[(f[3], int(f[2]))] = int(f[1])
    return ins, outs


def patterns(sv: Path, signal: str):
    pat = re.compile(rf"\(\({re.escape(signal)}\[31:0\] & 32'h([0-9a-f]+)\) == 32'h([0-9a-f]+)\)")
    return sorted(set(pat.findall(sv.read_text())))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--run", type=Path, required=True, help="run directory (synth.ys, *_yosys.aig, summary.json)")
    ap.add_argument("--yosys", default=None, help="yosys command used by the run (default from run kind)")
    ap.add_argument("--crisp-config", type=Path, help="CRISP config with channels (timing runs)")
    ap.add_argument("--channels", nargs="*", default=[], help="channel=maxlat for constrained channels")
    ap.add_argument("--word", default="instr_rdata_i", help="instruction word input")
    ap.add_argument("--profile", choices=("ports", "cva6"), default="ports",
                    help="ports: word and channels are top-level ports; cva6: CVA6 AXI structs and I$ SRAM lanes")
    ap.add_argument("--pattern-signal", default=None, help="signal named in the ISA assumptions (default --word)")
    ap.add_argument("--aligned-control-flow", action="store_true", help="see aligned(): stimulus refinement only")
    ap.add_argument("--reset", default="rst_ni")
    ap.add_argument("--cycles", type=int, default=1000)
    ap.add_argument("--rounds", type=int, default=16)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--rereset", type=int, default=2, help="per-mille probability of a later reset cycle")
    ap.add_argument("--abc-command", help="ABC command (default: the run's summary.json command)")
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    run, out = args.run.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)

    # 1. regenerate the AIGER with a map
    ys = (run / "synth.ys").read_text()
    m = re.search(r"write_aiger -zinit (\S+)", ys)
    recorded = Path(m.group(1))
    regen = out / "pre.aig"
    ys2 = ys.replace(m.group(0), f"write_aiger -zinit -map {out/'pre.map'} {regen}")
    (out / "synth_map.ys").write_text(ys2)
    yosys = args.yosys.split() if args.yosys else ["synlig"]
    subprocess.run(yosys + ["-q", "-s", str(out / "synth_map.ys")], cwd=run, check=True, capture_output=True)
    identical = sha(regen) == sha(recorded)
    if not identical:
        raise SystemExit(f"regenerated AIGER differs from {recorded}")

    # 2. post-ABC model from the run's ABC command
    if args.abc_command:
        cmd = args.abc_command
    else:
        cmd = json.loads((run / "summary.json").read_text())["abc_command"]
    cmd = re.sub(r"read_aiger [^;\s]+", f"read_aiger {regen}", cmd)
    cmd = re.sub(r"write_aiger [^;\s]+", f"write_aiger {out/'post.aig'}", cmd)
    cmd = cmd.replace(" print_stats;", "")
    abc = subprocess.run(["abc", "-c", cmd], capture_output=True, text=True)
    (out / "abc.log").write_text(abc.stdout + abc.stderr)
    if abc.returncode or not (out / "post.aig").exists():
        raise SystemExit("abc failed")

    # 3. spec
    ins, outs = parse_map(out / "pre.map")
    spec = [f"reset_n {ins[(args.reset, 0)]}", f"rereset {args.rereset}"]
    isa = list(run.glob("assumptions_isa.sv")) or list(run.glob("**/isa.sv"))
    if args.profile == "cva6":
        pats = patterns(isa[0], args.pattern_signal or "pscorr_isa_word") if isa else []
        if args.aligned_control_flow:
            pats = aligned(pats)
        spec += cva6_spec(ins, outs, pats, args.channels)
    elif (args.word, 0) in ins:
        spec.append("word " + " ".join(str(ins[(args.word, b)]) for b in range(32)))
        if isa:
            for mask, val in patterns(isa[0], args.word):
                spec.append(f"pattern {mask} {val}")
    if args.channels and args.profile == "ports":
        import yaml
        chans = yaml.safe_load(args.crisp_config.read_text())["signals"]["channels"]
        for item in args.channels:
            name, lat = item.split("=")
            c = chans[name]
            if "req_ready" in c:
                spec.append(f"const1 {ins[(c['req_ready'], 0)]}")
            rdy = outs[(c["rsp_ready"], 0)] if "rsp_ready" in c else -1
            if "req_tag" in c:
                tw = int(c["tag_width"])
                spec.append(" ".join(["tagged", lat, str(outs[(c["req_valid"], 0)]), str(rdy), str(ins[(c["rsp_valid"], 0)]),
                                      "-1", str(tw)] + [str(outs[(c["req_tag"], b)]) for b in range(tw)]
                                     + [str(ins[(c["rsp_tag"], b)]) for b in range(tw)]))
            else:
                spec.append(" ".join(["inorder", lat, str(outs[(c["req_valid"], 0)]), str(rdy), str(ins[(c["rsp_valid"], 0)])]))
    (out / "spec.txt").write_text("\n".join(spec) + "\n")

    exe = out / "aigcosim"
    # -B/usr/bin: a RISC-V assembler earlier on PATH would otherwise shadow the host one
    subprocess.run(["/usr/bin/gcc", "-O2", "-B/usr/bin/", "-o", str(exe), str(CSIM)], check=True)
    sim = subprocess.run([str(exe), str(regen), str(out / "post.aig"), str(out / "spec.txt"),
                          str(args.cycles), str(args.rounds), str(args.seed)], capture_output=True, text=True)
    (out / "sim.log").write_text(sim.stdout + sim.stderr)
    res = json.loads(sim.stdout.strip().splitlines()[-1])
    rec = {"run": str(run), "recorded_aig_sha256": sha(recorded), "regenerated_identical": identical,
           "abc_command": cmd, "post_sha256": sha(out / "post.aig"), "spec_lines": len(spec),
           "patterns": sum(1 for s in spec if s.startswith("pattern")), "channels": args.channels,
           "cosim_source_sha256": sha(CSIM), "result": res,
           "status": "match" if res["mismatch_trace_cycles"] == 0 else "MISMATCH"}
    (out / "summary.json").write_text(json.dumps(rec, indent=2) + "\n")
    print(json.dumps({"status": rec["status"], **res}))
    return 0 if rec["status"] == "match" else 1


if __name__ == "__main__":
    raise SystemExit(main())
