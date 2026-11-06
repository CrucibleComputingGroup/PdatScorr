#!/usr/bin/env python3
"""Run the Pscorr flow (CRISP -> SVA -> scorr) on unchanged CVA6 (stock cv32a60x, HPDcache).

The same steps and options as len5/run_len5.py, with CVA6's frontend:
- sources: the file list of the CVA6 elaboration survey (CVA6 d33a4fb9 plus its pinned
  hpdcache and cvfpu submodules), read with yosys-slang; CVA6's own assertions and
  covers are removed, CRISP assumptions are kept;
- SRAM macros (I$ sram_cache, D$ hpdcache_sram_*) are black boxes; `expose -evert`
  turns their pins into top-level ports, so read data is unconstrained and the logic
  driving addresses, write data and enables stays observed;
- ISA assumptions are injected into id_stage on the decoder input of a valid fetch entry
  (pscorr_isa_word below); interface timing and the reset-first assumption go into cva6.
"""
from __future__ import annotations

import argparse
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
sys.path.insert(0, str(HERE.parent / "len5"))
from make_synthesis_script import _generate_synthesis_commands  # noqa: E402
from run_len5 import ABC, CRISP_DEFAULT, RESET_FIRST, YOSYS_SLANG, abc_stats, run, sha  # noqa: E402

WS = Path("/home/allenjin/Projects/DAC_pscorr")
SURVEY = WS / "experiments/bounded_dynamic/stock_pscorr/build/cva6_survey_v1"
CORE = WS / "code/PdatProject/CoreSim/cores/cva6/core"
TOP = "cva6"
BLACKBOXES = ["sram_cache", "hpdcache_sram_1rw", "hpdcache_sram_wbyteenable_1rw", "hpdcache_sram_wmask_1rw"]
ISA_WORD = """
  // Pscorr: the decoder input of a valid fetch entry (a NOP otherwise), the word the
  // CRISP ISA assumptions constrain.
  wire [31:0] pscorr_isa_word = fetch_entry_valid_i[0] ? instruction_deco[0] : 32'h00000013;
"""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dsl", type=Path)
    ap.add_argument("--config", type=Path, default=HERE / "cva6_crisp.yaml")
    ap.add_argument("--crisp", type=Path, default=CRISP_DEFAULT)
    ap.add_argument("--depth", type=int, default=5)
    ap.add_argument("--flow", choices=("stock", "reset"), default="reset")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--skip-gates", action="store_true")
    ap.add_argument("--abc-timeout", type=int, default=86400)
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    rec: dict = {"script_sha256": sha(Path(__file__)), "depth": args.depth, "top": TOP, "flow": args.flow,
                 "survey_dir": str(SURVEY), "filelist_sha256": sha(SURVEY / "files_hpd.f")}

    isa_code, top_code = "", ""
    if args.dsl:
        env = dict(os.environ, PYTHONPATH=str(args.crisp))
        rc, _ = run([sys.executable, "-m", "pdat_dsl", "codegen", "--config", str(args.config.resolve()),
                     str(args.dsl.resolve()), str(out / "assumptions_isa.sv")], out, out / "codegen.log", env)
        if rc:
            raise SystemExit(f"codegen failed: {out/'codegen.log'}")
        isa_code = ISA_WORD + (out / "assumptions_isa.sv").read_text()
        timing = out / "assumptions_isa_timing.sv"
        if timing.exists():
            top_code += timing.read_text()
            rec["assumptions_timing_sha256"] = sha(timing)
        rec.update(dsl=str(args.dsl.resolve()), dsl_sha256=sha(args.dsl), crisp_checkout=str(args.crisp),
                   crisp_head=subprocess.run(["git", "-C", str(args.crisp), "rev-parse", "HEAD"],
                                             capture_output=True, text=True).stdout.strip(),
                   config_sha256=sha(args.config), assumptions_isa_sha256=sha(out / "assumptions_isa.sv"))
    if args.flow == "reset":
        top_code += RESET_FIRST

    files = [l.strip() for l in (SURVEY / "files_hpd.f").read_text().splitlines() if l.strip()]
    for name, code in (("id_stage.sv", isa_code), ("cva6.sv", top_code)):
        src = CORE / name
        dst = out / name
        if code:
            (out / f"inject_{name}").write_text(code)
            subprocess.run([sys.executable, str(REPO / "scripts/inject_checker.py"), "--assumptions-file",
                            str(out / f"inject_{name}"), str(src), str(dst)], check=True, stdout=subprocess.DEVNULL)
        else:
            shutil.copyfile(src, dst)
        files = [str(dst) if f == str(src) else f for f in files]
    (out / "files.f").write_text("\n".join(files) + "\n")
    bb = " ".join(f"--blackboxed-module {m}" for m in BLACKBOXES)
    stock = _generate_synthesis_commands(TOP, str(out / "cva6"))
    anchor = "flatten\n"
    assert stock.count(anchor) == 1
    stock = stock.replace(anchor, anchor + "\n# SRAM macros: pins become top-level ports (read data unconstrained)\n"
                          "expose -evert t:*sram*\n", 1)
    script = (f"read_slang -j 8 --top {TOP} --no-implicit-memories -D SYNTHESIS -D HPDCACHE_ASSERT_OFF {bb} -f files.f\n"
              f"delete {' '.join('=' + m for m in BLACKBOXES)}\n"
              f"read_verilog -sv -lib -defer {SURVEY/'bb/sram_cache_bb.sv'} {SURVEY/'bb/hpdcache_sram_bb.sv'}\n"
              "# CVA6's own assertions and covers are not part of the contract; CRISP assumptions stay\n"
              f"hierarchy -top {TOP}\nchformal -assert -remove\nchformal -cover -remove\n" + stock)
    (out / "synth.ys").write_text(script)
    rc, rec["yosys_seconds"] = run([str(YOSYS_SLANG), "-m", "slang", "-q", "-s", "synth.ys"], out, out / "yosys.log")
    if rc:
        raise SystemExit(f"yosys failed: {out/'yosys.log'}")
    aig = out / "cva6_yosys.aig"
    pre = abc_stats(subprocess.run([ABC, "-c", f"read_aiger {aig}; print_stats"], capture_output=True, text=True).stdout)[0]
    rec["yosys_aig"] = pre
    real = pre["po"] - pre["c"]
    removes = "".join(f" removepo -N {i};" for i in range(pre["po"] - 1, real - 1, -1))
    cycle = " cycle 100;" if args.flow == "stock" else ""
    cmd = (f"read_aiger {aig}; strash;{cycle} scorr -c -m -F {args.depth} -C 30000 -S 20 -v;"
           + (f" constr -r;{removes}" if pre["c"] else "")
           + f" rewrite -l; balance -l; print_stats; write_aiger {out/'cva6_post_abc.aig'}")
    rec["abc_command"] = cmd
    rc, rec["abc_seconds"] = run([ABC, "-c", cmd], out, out / "abc.log", timeout=args.abc_timeout)
    post = abc_stats((out / "abc.log").read_text())
    rec["post_abc"] = post[-1] if post else None
    if rc or not post:
        (out / "summary.json").write_text(json.dumps(rec, indent=2) + "\n")
        raise SystemExit(f"abc failed: {out/'abc.log'}")
    if not args.skip_gates:
        rc, rec["gates_seconds"] = run(["bash", str(REPO / "scripts/synth_to_gates.sh"), str(out / "cva6"), "",
                                        "clk_i", "cva6"], out, out / "gates_run.log")
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
