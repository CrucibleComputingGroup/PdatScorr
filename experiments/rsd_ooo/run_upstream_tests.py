#!/usr/bin/env python3
"""Run pinned RSD RTL tests with explicit completion and full output checks.

Unlike upstream RunTest.py, a timeout or a truncated serial prefix is a failure.
Every test receives a fresh output directory, avoiding stale register outputs.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path
import xml.etree.ElementTree as ET
from rsd_log_checks import assertion_diagnostics

ROOT = Path(__file__).resolve().parent
DEFAULT_TESTS = ["Asm/DynamicRecovery", "Asm/MemoryDependencyPrediction",
                 "Asm/ReplayQueueTest", "C/DCache", "Asm/LoadAndStoreZynq",
                 "Asm/UncachableLoadAndStore", "Asm/CacheFlush", "Asm/Fence"]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--binary", type=Path, required=True)
    p.add_argument("--source", type=Path, default=ROOT / "rsd")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--tests", nargs="+", default=DEFAULT_TESTS)
    p.add_argument("--cycle-multiplier", type=int, default=20)
    args = p.parse_args()
    binary = args.binary.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    summary = {"binary": str(binary), "binary_sha256": sha(binary), "tests": []}
    for test in args.tests:
        src = args.source.resolve() / "Processor/Src/Verification/TestCode" / test
        dst = output / test.replace("/", "_")
        dst.mkdir()
        for name in ("code.hex", "cfg.xml", "serial.ref.txt"):
            if (src / name).exists():
                shutil.copy2(src / name, dst / name)
        cfg = ET.parse(dst / "cfg.xml").getroot()
        limit = max(100000, int(cfg.findtext("MaxTestCycles")) * args.cycle_multiplier)
        cmd = [str(binary), "TEST_CODE=" + str(dst), f"MAX_TEST_CYCLES={limit}",
               "ENABLE_PC_GOAL=1", "SHOW_SERIAL_OUT=1"]
        result = {"test": test, "command": cmd, "cycle_limit": limit,
                  "input_sha256": sha(dst / "code.hex")}
        try:
            run = subprocess.run(cmd, cwd=args.source.resolve() / "Processor/Src",
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 text=True, errors="replace", timeout=180)
            log = run.stdout
            result["exit_code"] = run.returncode
        except subprocess.TimeoutExpired as e:
            log = e.stdout or b""
            if isinstance(log, bytes):
                log = log.decode(errors="replace")
            result["exit_code"] = None
            result["wall_timeout"] = True
        (dst / "simulation.log").write_text(log)
        result['log_sha256'] = sha(dst/'simulation.log')
        result["pc_goal_reached"] = "PC reached PC_GOAL:" in log
        result["register_mismatches"] = []
        regs = []
        if (dst / "reg.out.hex").exists():
            try:
                regs = [int(v.strip(), 0) for v in (dst / "reg.out.hex").read_text().splitlines()]
            except ValueError:
                pass
        expected = list(cfg.find("RegisterValues"))
        result["registers_checked"] = len(expected)
        for node in expected:
            key = node.tag
            index = 32 if key == "PC" else (33 + int(key[1:]) if key.startswith("f") else int(key[1:]))
            value = int(node.text.strip(), 0) & 0xffffffff
            actual = regs[index] if index < len(regs) else None
            if actual != value:
                result["register_mismatches"].append({"register": key, "expected": value, "actual": actual})
        result["serial_exact_match"] = True
        if (dst / "serial.ref.txt").exists():
            ref = (dst / "serial.ref.txt").read_bytes().replace(b"\r", b"")
            actual = (dst / "serial.out.txt").read_bytes().replace(b"\r", b"") if (dst / "serial.out.txt").exists() else None
            result["serial_exact_match"] = actual == ref
            result["serial_expected_bytes"] = len(ref)
            result["serial_actual_bytes"] = None if actual is None else len(actual)
        for label, field in [("Elapsed cycles", "cycles"), ("Num of committed RISC-V-ops", "instructions"),
                             ("Num of D$ load misses", "load_misses"), ("Num of D$ store misses", "store_misses"),
                             ("Num of memory dependency prediction misses", "memory_dependency_misses")]:
            match = re.search(re.escape(label) + r": (\d+)", log)
            if match:
                result[field] = int(match.group(1))
        result['within_cycle_limit'] = result.get('cycles',limit) < limit-1
        result['named_rsd_assertion_diagnostics'] = assertion_diagnostics(log)
        result['no_assertion_failure'] = not (result['named_rsd_assertion_diagnostics'] or re.search(r'Assertion failed|%Error|Exception caused',log))
        result['architectural_checks_passed'] = (result.get("exit_code") == 0 and result["pc_goal_reached"]
                            and result['within_cycle_limit']
                            and bool(expected) and not result["register_mismatches"]
                            and result["serial_exact_match"])
        result['passed'] = result['architectural_checks_passed'] and result['no_assertion_failure']
        (dst / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        summary["tests"].append(result)
        (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        print(f"{test}: {'PASS' if result['passed'] else 'FAIL'}, cycles={result.get('cycles')}", flush=True)
    return 0 if all(t["passed"] for t in summary["tests"]) else 1

if __name__ == "__main__":
    raise SystemExit(main())
