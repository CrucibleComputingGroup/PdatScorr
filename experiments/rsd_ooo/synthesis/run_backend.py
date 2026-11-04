#!/usr/bin/env python3
"""Run Pscorr's inductive correspondence and matched SKY130 mapping on an AIG.

No random-state cycling is performed. The constrained AIG and all logs remain
available; proof-only assumptions are purged only after inductive optimization.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import time
from pathlib import Path


def header(path):
    with path.open("rb") as f:
        line = f.readline().decode("ascii").split()
    if line[0] not in ("aig", "aag"):
        raise ValueError(f"Not AIGER: {path}")
    vals = list(map(int, line[1:])) + [0] * 4
    return dict(zip(("variables", "inputs", "latches", "outputs", "ands", "bad", "constraints", "justice", "fairness"), vals))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("input", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--depth", type=int, default=2)
    p.add_argument("--timeout", type=int, default=3600)
    p.add_argument("--no-scorr", action="store_true", help="Matched combinational mapping control; purge assumptions without using them")
    p.add_argument("--constant-only", action="store_true", help="Restrict scorr candidates to constants (-k); separate conservative scalability control")
    p.add_argument("--prebalance", action="store_true", help="Boolean balance -l before scorr; preserve the original read/strash statistics too")
    p.add_argument("--logic-only", action="store_true", help="Finish after successful scorr and output checks; no formal-AIG cell mapping")
    p.add_argument("--yosys", default=shutil.which("yosys"))
    p.add_argument("--abc", default=shutil.which("abc"))
    p.add_argument("--liberty", type=Path, default=Path("/opt/pdk/skywater-pdk/libraries/sky130_fd_sc_hd/latest/timing/sky130_fd_sc_hd__tt_025C_1v80.lib"))
    args = p.parse_args()
    if args.no_scorr and args.constant_only:
        p.error("--constant-only requires scorr")
    source, out = args.input.resolve(), args.output.resolve()
    if out.exists():
        raise SystemExit(f"Refusing existing output directory: {out}")
    out.mkdir(parents=True)
    initial = header(source)
    manifest = {"status": "running", "input": str(source), "input_sha256": hashlib.sha256(source.read_bytes()).hexdigest(), "initial": initial, "depth": args.depth, "scorr": not args.no_scorr, "candidate_scope": "constants_only" if args.constant_only else "full_correspondence" if not args.no_scorr else "none", "pre_scorr_balance": args.prebalance, "logic_only": args.logic_only, "cycle_initial_state": False, "liberty": str(args.liberty.resolve()), "stages": []}
    result = out / "result.json"
    def save():
        result.write_text(json.dumps(manifest, indent=2) + "\n")
    def run(command, log):
        start = time.monotonic()
        stage = {"command": command, "log": log, "status": "running"}
        manifest["stages"].append(stage)
        save()
        with (out / log).open("w") as f:
            try:
                proc = subprocess.run(command, stdout=f, stderr=subprocess.STDOUT, timeout=args.timeout, cwd=out)
                stage.update(status="passed" if proc.returncode == 0 else "failed", returncode=proc.returncode)
            except subprocess.TimeoutExpired:
                stage.update(status="timeout")
                raise
            finally:
                stage["elapsed_seconds"] = time.monotonic() - start
                save()
        if proc.returncode:
            raise RuntimeError(f"Stage failed: {log}")
    try:
        commands = [f"read_aiger {source}", "strash", "print_stats"]
        if args.prebalance:
            commands.extend(["balance -l", "print_stats", f"write_aiger {out / 'prebalanced.aig'}"])
        if not args.no_scorr:
            flags = "-c -m " if initial["constraints"] else ""
            if args.constant_only:
                flags += "-k "
            commands.append(f"scorr {flags}-F {args.depth} -C 30000 -S 20 -v")
            commands.extend(["print_stats", f"write_aiger {out / 'optimized_with_constraints.aig'}"])
        if initial["constraints"]:
            commands.append("constr -r -p")
        commands.extend(["rewrite -l", "balance -l", "print_stats", f"write_aiger {out / 'mapped_input.aig'}"])
        script = out / "optimize.abc"
        script.write_text("\n".join(commands) + "\n")
        run([args.abc, "-f", str(script)], "abc.log")
        final = header(out / "mapped_input.aig")
        if final["outputs"] != initial["outputs"] or final["constraints"]:
            raise RuntimeError("Output count changed or constraints survived purge")
        manifest["optimized"] = final
        if args.logic_only:
            manifest["status"] = "complete_logic"
            save()
            print(json.dumps({k: manifest[k] for k in ("status", "initial", "optimized")}, indent=2))
            return
        gate_script = out / "map.ys"
        gate_script.write_text(f"""read_aiger -clk_name clk {out / 'mapped_input.aig'}
flatten
opt
memory
opt_clean
fsm
opt
techmap
opt
dfflibmap -liberty {args.liberty.resolve()}
abc -liberty {args.liberty.resolve()} -fast
opt_clean
rename -top Core
write_verilog -noattr -noexpr -nohex {out / 'gates.v'}
tee -o {out / 'area.json'} stat -json -liberty {args.liberty.resolve()}
stat -liberty {args.liberty.resolve()}
""")
        run([args.yosys, "-Q", "-T", "-s", str(gate_script)], "mapping.log")
        log = (out / "mapping.log").read_text()
        areas = re.findall(r"Chip area for (?:top )?module[^:]*:\s*([\d.]+)", log)
        if areas:
            manifest["cell_area_um2"] = float(areas[-1])
        else:
            area_data = json.loads((out / "area.json").read_text())
            if sum(m["num_cells"] for m in area_data["modules"].values()) != 0:
                raise RuntimeError("Nonempty circuit but no mapped cell area reported")
            manifest["cell_area_um2"] = 0.0
        manifest["status"] = "complete"
    except BaseException as error:
        manifest["status"] = "failed"
        manifest["error"] = str(error)
        save()
        raise
    save()
    print(json.dumps({k: manifest[k] for k in ("status", "initial", "optimized", "cell_area_um2")}, indent=2))


if __name__ == "__main__":
    main()
