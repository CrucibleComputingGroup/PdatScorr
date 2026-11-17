#!/usr/bin/env python3
"""Microarchitecture-aware error injection for the single-cycle core (paper Section 4.2).

  inject.py RUN DST [--strict] [--control]

  RUN   a finished synth_core.sh run of one instruction subset. It supplies the injected
        top-level file with the CRISP assumption, the generated Yosys script and the
        list of permitted instructions.
  DST   output directory.

Steps:
  1. Candidates: the unit results of microarchitecture.json whose instructions are all
     forbidden by the constraint.
  2. Error injection: each candidate is forced to 0 in the netlist (a stuck-at fault),
     after `proc` in the flow's own Yosys script.
  3. Proof: the product of the original and the injected core, both starting in the reset
     state and under the constraint, must agree at the architectural observation boundary
     in every cycle. ABC proves this by 1-induction (scorr on the product); a candidate
     is accepted only if every disagreement output is proved constant 0. All candidates
     are tried together first, then one at a time on top of those already accepted.
  4. The core with the accepted injections goes through the flow's sweep and gate mapping.

--strict   observe the data-memory address and write data in every cycle instead of only
           in the cycles with a request.
--control  negative controls only: try to inject at every site whose instructions are
           permitted and at the address adder; each proof must fail.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import miter  # noqa: E402
import crosscheck  # noqa: E402

PREFIX = "riscvsinglecycle_optimized"
FLOW_ABC = ("read_aiger {inp}; strash; cycle 100; scorr -c -m -F 1 -C 30000 -S 20 -v; constr -r; "
            "removepo -N 98; rewrite -l; balance -l; print_stats; write_aiger {out}")
PROOF_ABC = "read_aiger {inp}; scorr -c -m -F 1 -C 30000 -S 20 -v; print_stats; write_aiger {out}"


def sh(cmd, log, cwd=None, env=None):
    with open(log, "w") as f:
        return subprocess.run(cmd, shell=True, stdout=f, stderr=subprocess.STDOUT, cwd=cwd, env=env).returncode


def permitted_instructions(run):
    text = open(os.path.join(run, PREFIX + "_assumptions.sv")).read()
    return set(re.findall(r"//\s*([A-Z]+)\s*$", text, re.M))


def yosys_script(run, dst, name, sites, reset_state):
    """The flow's generated script with stuck-at-0 injections after `proc`.
    reset_state: zero-initialize the flip-flops (for the proof) instead of the flow's
    free initial values."""
    lines = open(os.path.join(run, PREFIX + "_synth.ys")).read().split("\n")
    out, seen_proc = [], False
    for ln in lines:
        s = ln.strip()
        if s == "proc" and not seen_proc:
            seen_proc = True
            out.append(ln)
            for site in sites:
                out.append("connect -set %s %d'd0" % (site["signal"], site["width"]))
            if sites:
                out.append("setundef -undriven -zero")
            continue
        if s.startswith("setundef -zero") and reset_state:
            out.append("setundef -zero -init")
            continue
        if s.startswith("write_aiger"):
            # the port map must not end in .map: the front end reads *.map files in its directory
            out.append("write_aiger -zinit -map %s/%s.portmap %s/%s.aig" % (dst, name, dst, name))
            continue
        out.append(ln)
    assert seen_proc
    path = os.path.join(dst, name + ".ys")
    open(path, "w").write("\n".join(out))
    return path


def synthesize(run, dst, name, sites, reset_state):
    script = yosys_script(run, dst, name, sites, reset_state)
    env = dict(os.environ, SLPP_ALL=os.path.join(dst, "slpp_" + name))
    rc = sh("synlig -s %s" % os.path.basename(script), os.path.join(dst, name + "_yosys.log"), cwd=dst, env=env)
    subprocess.run("rm -rf %s" % env["SLPP_ALL"], shell=True)
    if rc != 0 or not os.path.isfile(os.path.join(dst, name + ".aig")):
        raise RuntimeError("front end failed for %s (see %s_yosys.log)" % (name, name))
    log = open(os.path.join(dst, name + "_yosys.log"), errors="replace").read()
    if "Treating undriven bit" in log:
        raise RuntimeError("undriven bits in %s" % name)
    return os.path.join(dst, name + ".aig")


def prove(dst, name, gold, sites, run, boundary, strict, always_run_proof=False, timeout=1800):
    """Inject `sites`, build the product with the original and try to prove agreement.

    Constrained-random simulation of the product runs first: a disagreement there rejects
    the injection without a proof attempt (unless always_run_proof), and a proved injection
    must show none. A proof that does not finish within `timeout` seconds rejects it."""
    t0 = time.time()
    gate = synthesize(run, dst, name, sites, reset_state=True)
    product = os.path.join(dst, name + "_product.aig")
    labels = miter.build(gold, gate, os.path.join(dst, "gold.portmap"), boundary, product, strict=strict)
    sim = crosscheck.simulate_product(product, os.path.join(dst, "gold.portmap"),
                                      os.path.join(run, PREFIX + "_assumptions.sv"))
    result = {"sites": [s["name"] for s in sites], "disagreements_checked": len(labels), "simulation": sim}
    if sim["first_disagreement_cycle"] is not None and not always_run_proof:
        result.update(proved=False, proof="not attempted: simulation shows a disagreement",
                      seconds=round(time.time() - t0, 1))
        return result
    swept = os.path.join(dst, name + "_product_swept.aig")
    rc = sh("timeout %d abc -c \"%s\"" % (timeout, PROOF_ABC.format(inp=product, out=swept)),
            os.path.join(dst, name + "_proof.log"))
    if rc == 124 or not os.path.isfile(swept):
        result.update(proved=False, proof="no result within %d s" % timeout, seconds=round(time.time() - t0, 1))
        return result
    open_props = miter.proved_outputs(swept, len(labels))
    if not open_props and sim["first_disagreement_cycle"] is not None:
        raise RuntimeError("%s: proved, but simulation shows a disagreement" % name)
    result.update(proved=not open_props, proof="1-induction on the product (ABC scorr)",
                  outputs_not_proved=len(open_props), examples=[labels[i] for i in open_props][:6],
                  seconds=round(time.time() - t0, 1))
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("dst")
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--control", action="store_true")
    a = ap.parse_args()
    run, dst = os.path.abspath(a.run), os.path.abspath(a.dst)
    os.makedirs(dst, exist_ok=True)
    desc = json.load(open(os.path.join(HERE, "microarchitecture.json")))
    boundary = desc["observation_boundary"]
    allowed = permitted_instructions(run)
    report = {"run": run, "permitted_instructions": sorted(allowed), "strict_boundary": a.strict}

    gold = synthesize(run, dst, "gold", [], reset_state=True)

    if a.control:
        controls = [s for s in desc["result_sites"] if set(s["instructions"]) & allowed] + desc["control_sites"]
        report["controls"] = [prove(dst, "control_" + s["name"], gold, [s], run, boundary, a.strict,
                                    always_run_proof=True) for s in controls]
        report["controls_all_rejected"] = all(not c["proved"] for c in report["controls"])
        json.dump(report, open(os.path.join(dst, "control_report.json"), "w"), indent=1)
        print(os.path.basename(dst), "controls:", " ".join(
            "%s=%s" % (c["sites"][0], "REJECTED" if not c["proved"] else "ACCEPTED(!)") for c in report["controls"]))
        return 0 if report["controls_all_rejected"] else 1

    candidates = [s for s in desc["result_sites"] if not (set(s["instructions"]) & allowed)]
    report["candidates"] = [s["name"] for s in candidates]
    accepted, proofs = [], []
    if candidates:
        joint = prove(dst, "inject_all", gold, candidates, run, boundary, a.strict)
        proofs.append(joint)
        if joint["proved"]:
            accepted = list(candidates)
        else:
            for s in candidates:
                p = prove(dst, "inject_" + "_".join(x["name"] for x in accepted + [s]), gold, accepted + [s],
                          run, boundary, a.strict)
                proofs.append(p)
                if p["proved"]:
                    accepted.append(s)
    report["proofs"] = proofs
    report["accepted"] = [s["name"] for s in accepted]

    # The core with the accepted injections through the flow's sweep and gate mapping.
    final = synthesize(run, dst, PREFIX + "_yosys", accepted, reset_state=False)
    base = os.path.join(dst, PREFIX)
    sh("abc -c \"%s\"" % FLOW_ABC.format(inp=final, out=base + "_post_abc.aig"), base + "_abc.log")
    flow = os.environ["PSCORR_SYNTHESIS_DIR"]
    sh("./scripts/synth_to_gates.sh %s \"\" clk RiscvSingleCycle_riscv_core" % base, base + "_gates_run.log", cwd=flow)
    area = None
    for line in open(base + "_gates.log", errors="replace"):
        if "Chip area for module" in line:
            area = float(line.split()[-1])
    report["area_um2"] = area
    json.dump(report, open(os.path.join(dst, "injection_report.json"), "w"), indent=1)
    print(os.path.basename(dst), "candidates:", ",".join(report["candidates"]) or "-",
          "accepted:", ",".join(report["accepted"]) or "-", "area:", area)
    return 0


if __name__ == "__main__":
    sys.exit(main())
