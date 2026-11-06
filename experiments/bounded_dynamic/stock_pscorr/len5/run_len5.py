#!/usr/bin/env python3
"""Run the stock Pscorr flow (CRISP -> SVA -> scorr) on the unchanged LEN5 datapath.

Steps, each the stock flow's own component unless noted:
1. CRISP -> SVA: `pdat_dsl codegen` with the LEN5 CRISP configuration.
2. Injection: scripts/inject_checker.py inserts the generated assumptions (plus any
   extra assumption files, e.g. generated interface-timing monitors) before the
   `endmodule` of datapath.sv, the module that owns the instruction-memory port.
3. Yosys: the stock command sequence (make_synthesis_script._generate_synthesis_commands)
   writes an AIGER whose constraints are the assumptions. Frontend: yosys-slang, because
   Synlig 0.33 cannot parse LEN5 (`foreach`); the mechanism test checks the two
   frontends give the same scorr result.
4. ABC: the stock command `strash; cycle 100; scorr -c -m -F k -C 30000 -S 20 -v`,
   then `constr -r`, removal of the constraint outputs, `rewrite -l; balance -l`.
5. Gate mapping: scripts/synth_to_gates.sh (SKY130 HD, tt corner).

Without --dsl, no CRISP assumption is injected: the same commands give the unconstrained
reference. The RTL source tree, top parameters and capacities are never changed.

--flow stock   exactly the stock ABC command, including `cycle 100`, whose random,
               unconstrained 100-cycle run supplies scorr's initial state.
--flow reset   reset is assumed in the first cycle (and is free afterwards), and
               `cycle 100` is dropped, so scorr's base case starts from reset. The
               mechanism test shows this gives deterministic results that match the
               exact reachable set, while `cycle 100` depends on the random run.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
sys.path.insert(0, str(REPO / "scripts"))
from make_synthesis_script import _generate_synthesis_commands  # noqa: E402

WS = Path("/home/allenjin/Projects/DAC_pscorr")
FRONTEND = WS / "experiments/bounded_dynamic/len5/build/pre_fpu_frontend"
YOSYS_SLANG = WS / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"
CRISP_DEFAULT = WS / "code/PdatProject/PdatDslBoundedDynamic"
ABC = "/usr/local/bin/abc"
TOP = "datapath"
ISA_WORD = """
  // Pscorr: the word entering the issue decoder from a valid issue-queue entry without a
  // fetch exception (a NOP otherwise); the word the CRISP ISA assumptions constrain.
  wire [31:0] pscorr_isa_word = (iq_cu_valid && !iq_data_out.except_raised) ? iq_data_out.instruction : 32'h00000013;
"""
ISA_WORD_VALID = """
  // Pscorr: the word entering the issue decoder from any valid issue-queue entry (a NOP
  // otherwise); the word the CRISP ISA assumptions constrain. Every value the issue
  // register latches (ireg_en = iq_cu_valid & cu_iq_ready) is then a constrained decode.
  wire [31:0] pscorr_isa_word = iq_cu_valid ? iq_data_out.instruction : 32'h00000013;
"""
RESET_FIRST = """
  // Pscorr reset semantics: reset is applied in the first cycle and is free afterwards
  logic pscorr_first_cycle_q = 1'b1;
  always_ff @(posedge clk_i) pscorr_first_cycle_q <= 1'b0;
  always_comb if (pscorr_first_cycle_q) assume (!rst_ni);
"""


def sha(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def abc_stats(text: str) -> list[dict]:
    pat = r"i/o =\s*(\d+)/\s*(\d+)(?:\s*\(c=(\d+)\))?\s+lat =\s*(\d+)\s+and =\s*(\d+)"
    return [{"pi": int(a), "po": int(b), "c": int(c or 0), "lat": int(d), "and": int(e)}
            for a, b, c, d, e in re.findall(pat, text)]


def run(cmd, cwd, log: Path, env=None, timeout=None) -> tuple[int, float]:
    t0 = time.time()
    with open(log, "w") as fh:
        p = subprocess.run(cmd, cwd=cwd, stdout=fh, stderr=subprocess.STDOUT, env=env, timeout=timeout)
    return p.returncode, round(time.time() - t0, 2)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dsl", type=Path, help="CRISP file; omit for the unconstrained reference")
    ap.add_argument("--extra-sva", type=Path, nargs="*", default=[], help="additional assumption code to inject")
    ap.add_argument("--config", type=Path, default=HERE / "len5_crisp.yaml")
    ap.add_argument("--crisp", type=Path, default=CRISP_DEFAULT, help="CRISP generator checkout")
    ap.add_argument("--depth", type=int, default=5)
    ap.add_argument("--flow", choices=("stock", "reset"), default="reset")
    ap.add_argument("--isa-site", choices=("port", "decoder", "decoder-valid"), default="port",
                    help="port: instr_rdata_i at the datapath; decoder: the issue decoder input of valid "
                         "entries without a fetch exception; decoder-valid: of every valid entry")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--skip-gates", action="store_true")
    ap.add_argument("--abc-timeout", type=int, default=86400)
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    rec: dict = {"script_sha256": sha(Path(__file__)), "depth": args.depth, "top": TOP, "flow": args.flow,
                 "isa_site": args.isa_site,
                 "frontend_dir": str(FRONTEND), "frontend_manifest_sha256": sha(FRONTEND / "manifest.json")}

    # 1-2. CRISP -> SVA, injection
    code, isa_code = "", ""
    if args.dsl:
        env = dict(os.environ, PYTHONPATH=str(args.crisp))
        rc, secs = run([sys.executable, "-m", "pdat_dsl", "codegen", "--config", str(args.config.resolve()),
                        str(args.dsl.resolve()), str(out / "assumptions_isa.sv")], out, out / "codegen.log", env)
        if rc:
            raise SystemExit(f"codegen failed: {out/'codegen.log'}")
        if args.isa_site in ("decoder", "decoder-valid"):
            word = ISA_WORD if args.isa_site == "decoder" else ISA_WORD_VALID
            isa_code = word + (out / "assumptions_isa.sv").read_text()
        else:
            code += (out / "assumptions_isa.sv").read_text()
        timing = out / "assumptions_isa_timing.sv"
        if timing.exists():
            code += "\n" + timing.read_text()
            rec["assumptions_timing_sha256"] = sha(timing)
        rec.update(dsl=str(args.dsl.resolve()), dsl_sha256=sha(args.dsl), crisp_checkout=str(args.crisp),
                   crisp_head=subprocess.run(["git", "-C", str(args.crisp), "rev-parse", "HEAD"],
                                             capture_output=True, text=True).stdout.strip(),
                   crisp_codegen_sha256=sha(args.crisp / "pdat_dsl/codegen.py"),
                   config_sha256=sha(args.config), assumptions_isa_sha256=sha(out / "assumptions_isa.sv"))
    for extra in args.extra_sva:
        code += "\n" + extra.read_text()
    rec["extra_sva"] = {str(p.resolve()): sha(p) for p in args.extra_sva}
    if args.flow == "reset":
        code += RESET_FIRST
    src = FRONTEND / "source/rtl/datapath.sv"
    dp = out / "datapath.sv"
    if code:
        (out / "assumptions_all.sv").write_text(code)
        subprocess.run([sys.executable, str(REPO / "scripts/inject_checker.py"), "--assumptions-file",
                        str(out / "assumptions_all.sv"), str(src), str(dp)], check=True, stdout=subprocess.DEVNULL)
    else:
        shutil.copyfile(src, dp)

    # 3. Yosys (stock commands)
    files = (FRONTEND / "frontend.ys").read_text().splitlines()[0].split()
    files = [f for f in files if f.endswith(".sv")]
    files = [str(dp) if f == "source/rtl/datapath.sv" else str(FRONTEND / f) for f in files]
    if isa_code:
        isrc = FRONTEND / "source/rtl/expipe/issue-unit/issue_stage.sv"
        (out / "inject_issue_stage.sv").write_text(isa_code)
        subprocess.run([sys.executable, str(REPO / "scripts/inject_checker.py"), "--assumptions-file",
                        str(out / "inject_issue_stage.sv"), str(isrc), str(out / "issue_stage.sv")],
                       check=True, stdout=subprocess.DEVNULL)
        files = [str(out / "issue_stage.sv") if f == str(isrc) else f for f in files]
    script = (f"read_slang --single-unit --no-implicit-memories --top {TOP} -D SYNTHESIS {' '.join(files)}\n"
              + _generate_synthesis_commands(TOP, str(out / "len5")))
    (out / "synth.ys").write_text(script)
    rc, rec["yosys_seconds"] = run([str(YOSYS_SLANG), "-m", "slang", "-q", "-s", "synth.ys"], out, out / "yosys.log")
    if rc:
        raise SystemExit(f"yosys failed: {out/'yosys.log'}")
    aig = out / "len5_yosys.aig"
    pre = abc_stats(subprocess.run([ABC, "-c", f"read_aiger {aig}; print_stats"], capture_output=True, text=True).stdout)[0]
    rec["yosys_aig"] = pre

    # 4. ABC (stock command)
    real = pre["po"] - pre["c"]
    removes = "".join(f" removepo -N {i};" for i in range(pre["po"] - 1, real - 1, -1))
    cycle = " cycle 100;" if args.flow == "stock" else ""
    cmd = (f"read_aiger {aig}; strash;{cycle} scorr -c -m -F {args.depth} -C 30000 -S 20 -v;"
           + (f" constr -r;{removes}" if pre["c"] else "")
           + f" rewrite -l; balance -l; print_stats; write_aiger {out/'len5_post_abc.aig'}")
    rec["abc_command"] = cmd
    rc, rec["abc_seconds"] = run([ABC, "-c", cmd], out, out / "abc.log", timeout=args.abc_timeout)
    rec["abc_returncode"] = rc
    post = abc_stats((out / "abc.log").read_text())
    rec["post_abc"] = post[-1] if post else None
    if rc or not post:
        (out / "summary.json").write_text(json.dumps(rec, indent=2) + "\n")
        raise SystemExit(f"abc failed: {out/'abc.log'}")

    # 5. Gate mapping (stock script)
    if not args.skip_gates:
        rc, rec["gates_seconds"] = run(["bash", str(REPO / "scripts/synth_to_gates.sh"), str(out / "len5"), "",
                                        "clk_i", "len5"], out, out / "gates_run.log")
        log = (out / "gates_run.log").read_text()
        m = re.findall(r"Chip area for (?:top )?module '[^']*':\s*([0-9.]+)", log)
        cells = re.findall(r"Number of cells:\s*(\d+)", log)
        rec.update(gates_returncode=rc, cell_area=float(m[-1]) if m else None, cells=int(cells[-1]) if cells else None)
    rec["status"] = "ok"
    (out / "summary.json").write_text(json.dumps(rec, indent=2) + "\n")
    print(json.dumps({k: rec.get(k) for k in ("status", "yosys_aig", "post_abc", "abc_seconds", "cell_area", "cells")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
