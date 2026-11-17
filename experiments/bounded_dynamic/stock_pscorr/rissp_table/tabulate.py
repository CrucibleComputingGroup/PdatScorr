#!/usr/bin/env python3
"""Collect the runs of regenerate.sh into results/*.csv.

  tabulate.py OUT SAVED RESULTS

  OUT      output directory of regenerate.sh
  SAVED    the saved runs behind the paper's RISSP column
           (PdatCoreSim/cores/RiscvSingleCycle/synthesis_results)
  RESULTS  directory for the CSV files

Every netlist is tested at the instruction level on the instructions of its own subset
(tools/coretest.py); the column "failing" lists the instructions whose result differs
from the RV32 reference for at least one operand pair.
"""
import csv
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "tools"))
import coretest as ct  # noqa: E402

CFGS = ["%d%d%d%d" % (m, d, a, s) for m in (0, 1) for d in (0, 1) for a in (0, 1) for s in (0, 1)]

# Paper Table 1 as published: configuration -> (RISSP, PwF) in square micrometres.
PUBLISHED = {
    "0000": (33148.04, 32205.90), "0001": (36862.85, 35661.70), "0010": (35940.72, 32205.90),
    "0011": (39303.95, 35609.20), "0100": (60857.12, 31996.90), "0101": (64291.66, 35521.60),
    "0110": (63397.05, 31950.60), "0111": (66939.20, 35376.40), "1000": (85254.27, 77455.50),
    "1001": (82890.75, 81249.20), "1010": (85784.77, 77583.20), "1011": (88697.57, 80835.00),
    "1100": (81197.88, 77586.90), "1101": (83980.54, 80808.80), "1110": (100503.89, 77327.90),
    "1111": (104164.90, 80835.00),
}


def area(log):
    value = None
    if os.path.isfile(log):
        for line in open(log, errors="replace"):
            if "Chip area for module" in line:
                value = float(line.split()[-1])
    return value


def ands(aig):
    with open(aig, "rb") as f:
        return int(f.readline().split()[5])


def depth(aig_path):
    """Logic depth (AND levels) of the netlist; a combinational 32-bit divider is several hundred."""
    aig = ct.read_aig(aig_path)
    lev = [0] * (aig["M"] + 1)
    base = 1 + aig["I"] + aig["L"]
    for k, (r0, r1) in enumerate(aig["ands"]):
        lev[base + k] = 1 + max(lev[r0 >> 1], lev[r1 >> 1])
    return max(lev)


def abc_seconds(log):
    """Run time that ABC reports for the induction proof on the product machine."""
    value = ""
    if os.path.isfile(log):
        for line in open(log, errors="replace"):
            if line.startswith("TOTAL"):
                value = "%.1f" % float(line.split("=")[1].split("sec")[0])
    return value


def failing(aig, mapfile, cfg, operands):
    spec = "mul=%s,div=%s,add=%s,shift=%s" % tuple(cfg)
    names = ct.allowed_set(spec)
    core = ct.Core(aig, mapfile)
    bad = []
    for n in names:
        ok, tot = ct.test_instruction(core, n, *operands)
        if ok != tot:
            bad.append(n)
    return len(names), " ".join(bad)


def write(path, cols, rows):
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        for r in rows:
            w.writerow({c: r.get(c, "") for c in cols})


def main():
    out, saved, results = sys.argv[1:4]
    os.makedirs(results, exist_ok=True)
    operands = ct.operands(random.Random(11))
    pwf_map = os.path.join(out, "maps", "pwf.portmap")
    saved_map = os.path.join(out, "maps", "saved.portmap")

    def unit_flags(cfg):
        return {"config": cfg, "mul": cfg[0], "div": cfg[1], "add": cfg[2], "shift": cfg[3]}

    # 1. The saved runs behind the published RISSP column.
    rows = []
    for cfg in CFGS:
        d = os.path.join(saved, "mul%s_div%s_add%s_shift%s" % tuple(cfg))
        r = unit_flags(cfg)
        r["published_um2"] = "%.2f" % PUBLISHED[cfg][0]
        r["saved_um2"] = "%.2f" % float(open(os.path.join(d, "total_area.txt")).read())
        aig = os.path.join(d, "post_abc.aig")
        r["and_gates"] = ands(aig)
        r["logic_depth"] = depth(aig)
        r["tested"], r["failing"] = failing(aig, saved_map, cfg, operands)
        rows.append(r)
    write(os.path.join(results, "published_rissp_column.csv"),
          ["config", "mul", "div", "add", "shift", "published_um2", "saved_um2", "and_gates", "logic_depth",
           "tested", "failing"], rows)

    # 2. PwF flow on the paper-era core and on the minimal-fix core.
    for core, name in (("paper", "published_pwf_column.csv"), ("minfix", "minfix_pwf.csv")):
        rows = []
        for cfg in CFGS:
            p = os.path.join(out, "pwf_" + core, cfg, "riscvsinglecycle_optimized")
            r = unit_flags(cfg)
            r["published_um2"] = "%.2f" % PUBLISHED[cfg][1]
            r["regenerated_um2"] = "%.2f" % area(p + "_gates.log")
            r["and_gates"] = ands(p + "_post_abc.aig")
            r["logic_depth"] = depth(p + "_post_abc.aig")
            r["tested"], r["failing"] = failing(p + "_post_abc.aig", pwf_map, cfg, operands)
            rows.append(r)
        write(os.path.join(results, name),
              ["config", "mul", "div", "add", "shift", "published_um2", "regenerated_um2", "and_gates",
               "logic_depth", "tested", "failing"], rows)

    # 3. Corrected core: module-level baseline, PwF without and with error injection.
    #    The paper's table uses the runs in which the constraint holds in every cycle
    #    (pwf_fixed_inreset); the runs with the generated constraint, which exempts the
    #    cycles with reset asserted (pwf_fixed), are tabulated beside them.
    names = ["published_rissp_column.csv", "published_pwf_column.csv", "minfix_pwf.csv"]
    for runs, suffix in (("pwf_fixed_inreset", ""), ("pwf_fixed", "_reset_exempt")):
        rows, inj_rows, ctl_rows = [], [], []
        for cfg in CFGS:
            b = os.path.join(out, "base_fixed", cfg, "baseline")
            p = os.path.join(out, runs, cfg, "riscvsinglecycle_optimized")
            e = os.path.join(out, runs + "_inject", cfg, "riscvsinglecycle_optimized")
            r = unit_flags(cfg)
            ba, pa, ea = area(b + "_gates.log"), area(p + "_gates.log"), area(e + "_gates.log")
            r["baseline_um2"] = "%.2f" % ba
            r["baseline_and_gates"] = ands(b + "_post_abc.aig")
            r["baseline_tested"], r["baseline_failing"] = failing(b + "_post_abc.aig", b + ".portmap", cfg, operands)
            r["sweep_only_um2"] = "%.2f" % pa
            r["sweep_only_and_gates"] = ands(p + "_post_abc.aig")
            r["sweep_only_tested"], r["sweep_only_failing"] = failing(p + "_post_abc.aig", pwf_map, cfg, operands)
            r["sweep_only_vs_baseline_pct"] = "%+.2f" % (100.0 * (pa / ba - 1.0))
            r["pwf_um2"] = "%.2f" % ea
            r["pwf_and_gates"] = ands(e + "_post_abc.aig")
            r["pwf_tested"], r["pwf_failing"] = failing(e + "_post_abc.aig", e + "_yosys.portmap", cfg, operands)
            r["pwf_vs_baseline_pct"] = "%+.2f" % (100.0 * (ea / ba - 1.0))
            rows.append(r)

            rep = json.load(open(os.path.join(out, runs + "_inject", cfg, "injection_report.json")))
            last = rep["proofs"][-1] if rep["proofs"] else None
            proof_log = os.path.join(out, runs + "_inject", cfg, "inject_all_proof.log")
            inj_rows.append(dict(
                unit_flags(cfg), candidates=" ".join(rep["candidates"]), accepted=" ".join(rep["accepted"]),
                proofs=len(rep["proofs"]),
                step_seconds="%.1f" % sum(x["seconds"] for x in rep["proofs"]),
                abc_proof_seconds=abc_seconds(proof_log) if last else "",
                disagreement_outputs=last["disagreements_checked"] if last else "",
                simulated_instructions=last["simulation"]["permitted_instructions_executed"] if last else "",
                simulated_disagreement="" if not last else (
                    "none" if last["simulation"]["first_disagreement_cycle"] is None else "yes")))
            ctl_path = os.path.join(out, runs + "_inject_control", cfg, "control_report.json")
            ctl = json.load(open(ctl_path)) if os.path.isfile(ctl_path) else {"controls": []}
            for c in ctl["controls"]:
                sim = c["simulation"]["first_disagreement_cycle"]
                ctl_rows.append(dict(config=cfg, site=c["sites"][0], proof="proved" if c["proved"] else "rejected",
                                     detail=c.get("proof", ""), outputs_not_proved=c.get("outputs_not_proved", ""),
                                     simulation="no disagreement" if sim is None else "disagreement in cycle %d" % sim,
                                     seconds="%.1f" % c["seconds"]))
        write(os.path.join(results, "corrected_core%s.csv" % suffix),
              ["config", "mul", "div", "add", "shift", "baseline_um2", "baseline_and_gates", "baseline_tested",
               "baseline_failing", "sweep_only_um2", "sweep_only_and_gates", "sweep_only_tested",
               "sweep_only_failing", "sweep_only_vs_baseline_pct", "pwf_um2", "pwf_and_gates", "pwf_tested",
               "pwf_failing", "pwf_vs_baseline_pct"], rows)
        write(os.path.join(results, "error_injection%s.csv" % suffix),
              ["config", "mul", "div", "add", "shift", "candidates", "accepted", "proofs", "step_seconds",
               "abc_proof_seconds", "disagreement_outputs", "simulated_instructions", "simulated_disagreement"],
              inj_rows)
        write(os.path.join(results, "error_injection_controls%s.csv" % suffix),
              ["config", "site", "proof", "detail", "outputs_not_proved", "simulation", "seconds"], ctl_rows)
        names += ["corrected_core%s.csv" % suffix, "error_injection%s.csv" % suffix,
                  "error_injection_controls%s.csv" % suffix]

    for name in names:
        print("==", name)
        with open(os.path.join(results, name)) as f:
            for line in f:
                print("  ", line.rstrip())


if __name__ == "__main__":
    main()
