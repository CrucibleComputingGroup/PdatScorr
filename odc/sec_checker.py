#!/usr/bin/env python3
"""Fail-closed sequential equivalence of explicit ABC design pairs.

Raw AIGER assumptions/properties are rejected, never stripped. Constrained
specialization needs an explicit shared-contract inductive miter backend.
This repairs the checker gate, not legacy injection/rewriting or Ibex results.
"""
import hashlib
import re
import subprocess
import time
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional, Tuple
from enum import Enum


class SecStatus(Enum):
    EQUIVALENT = "equivalent"
    NOT_EQUIVALENT = "not_equivalent"
    TIMEOUT = "timeout"
    ERROR = "error"
    UNKNOWN = "unknown"


@dataclass
class SecResult:
    status: SecStatus
    runtime_sec: float
    counterexample: Optional[str] = None
    abc_output: str = ""
    proof_completed: bool = False
    proof_method: Optional[str] = None
    returncode: Optional[int] = None
    synthetic: bool = False
    command: Tuple[str, ...] = ()
    input_sha256: dict = field(default_factory=dict)

    def __str__(self):
        result = f"SEC Result: {self.status.value.upper()} ({self.runtime_sec:.2f}s)"
        return result + (f"\nCounterexample: {self.counterexample}" if self.counterexample else "")

    @property
    def is_equivalent(self) -> bool:
        return (self.status == SecStatus.EQUIVALENT and self.proof_completed
                and bool(self.proof_method) and self.returncode == 0 and not self.synthetic)


class SecChecker:
    def __init__(self, abc_path="abc", conflict_limit=30000, timeout_sec=600):
        self.abc_path = abc_path
        self.conflict_limit = conflict_limit
        self.timeout_sec = timeout_sec

    @staticmethod
    def _inspect_aiger(path):
        with path.open('rb') as f:
            header = f.readline(4096).decode('ascii').strip().split()
        if (len(header) < 6 or len(header) > 10 or header[0] not in ('aig', 'aag')
                or any(not x.isdecimal() for x in header[1:])):
            raise ValueError(f"Unsupported or malformed AIGER header: {path}")
        values = [int(x) for x in header[1:]]
        # M I L O A [B C J F]: equal counts do not establish equal assumptions.
        if any(values[5:]):
            raise ValueError("AIGER assumptions/properties require an explicit shared-contract "
                             "inductive miter; this checker never removes constraints")
        if values[2] == 0 or values[3] == 0:
            raise ValueError("Expected a sequential design with a latch and observable output")
        # Do not let a backend silently turn arbitrary latch initialization into
        # zero initialization. AIGER defaults to zero; explicit 0/1 are supported.
        with path.open('rb') as f:
            f.readline()
            if header[0] == 'aag':
                for _ in range(values[1]):
                    f.readline()
            required = 2 if header[0] == 'aag' else 1
            for _ in range(values[2]):
                latch = f.readline(4096).decode('ascii').split()
                if (len(latch) not in (required, required+1)
                        or any(not x.isdecimal() for x in latch)):
                    raise ValueError("Malformed AIGER latch declaration")
                if len(latch) > required and int(latch[-1]) not in (0, 1):
                    raise ValueError("Arbitrary initial state requires an explicit inductive miter")
        return values[1], values[3]

    @staticmethod
    def _abc_path(path):
        text = str(path.resolve())
        # ABC parses commands even though subprocess does not use a shell.
        if any(c in text for c in (';', '"', '\\', '\n', '\r', '\x00')):
            raise ValueError("Path contains unsupported ABC command characters")
        return f'"{text}"'

    def _generate_sec_script(self, baseline_aig, modified_aig, k_depth):
        if k_depth < 1:
            raise ValueError("Induction depth must be positive")
        if baseline_aig.resolve() == modified_aig.resolve():
            raise ValueError("Baseline and candidate must be distinct files")
        # Zero-argument dsec uses current-network pSpec, not the earlier baseline.
        return (f"dsec -F {k_depth} -v {self._abc_path(baseline_aig)} "
                f"{self._abc_path(modified_aig)};")

    def check_equivalence(self, baseline_aig, modified_aig, k_depth=2):
        start = time.monotonic()
        command, hashes = (), {}
        try:
            baseline_aig, modified_aig = Path(baseline_aig), Path(modified_aig)
            script = self._generate_sec_script(baseline_aig, modified_aig, k_depth)
            if self._inspect_aiger(baseline_aig) != self._inspect_aiger(modified_aig):
                raise ValueError("Baseline/candidate input or observable-output counts differ")
            hashes = {str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in (baseline_aig, modified_aig)}
            command = (self.abc_path, '-c', script)
            run = subprocess.run(list(command), stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, text=True, timeout=self.timeout_sec)
            status, cex = self._parse_abc_output(run.stdout, run.returncode)
            if any(hashlib.sha256(Path(p).read_bytes()).hexdigest() != digest
                   for p, digest in hashes.items()):
                status, cex = SecStatus.ERROR, None
            return SecResult(status, time.monotonic()-start, cex, run.stdout,
                             proof_completed=status == SecStatus.EQUIVALENT,
                             proof_method='abc-dsec-explicit-pair', returncode=run.returncode,
                             command=command, input_sha256=hashes)
        except subprocess.TimeoutExpired as exc:
            output = exc.stdout or ''
            if isinstance(output, bytes):
                output = output.decode(errors='replace')
            return SecResult(SecStatus.TIMEOUT, time.monotonic()-start,
                             abc_output=output+'\nABC timeout', command=command,
                             input_sha256=hashes)
        except Exception as exc:
            return SecResult(SecStatus.ERROR, time.monotonic()-start,
                             abc_output=str(exc), command=command, input_sha256=hashes)

    def _parse_abc_output(self, output, returncode=0):
        if returncode != 0:
            return SecStatus.ERROR, None
        if re.search(r'\b(timeout|timed out|resource limit|time limit reached)\b', output, re.I):
            return SecStatus.TIMEOUT, None
        if (re.search(r'\b(error|failed|failure)\b', output, re.I)
                or re.search(r'(?im)^\s*(?:usage:|unknown command\b|cannot\b|'
                             r'the external spec is not given|the network has no latches)', output)):
            return SecStatus.ERROR, None
        statuses = re.findall(r'(?im)^\s*Networks are (equivalent|not equivalent|undecided)'
                              r'(?:\.| after [^\n]*\.)', output)
        verdicts = {s.lower() for s in statuses}
        if len(verdicts) != 1:
            return (SecStatus.ERROR if verdicts else SecStatus.UNKNOWN), None
        verdict = verdicts.pop()
        if verdict == 'equivalent':
            return SecStatus.EQUIVALENT, None
        if verdict == 'not equivalent':
            return SecStatus.NOT_EQUIVALENT, self._extract_counterexample(output)
        return SecStatus.UNKNOWN, None

    @staticmethod
    def _extract_counterexample(output):
        lines = [line.strip() for line in output.splitlines()
                 if any(x in line for x in ('Var', 'Input', 'PI'))]
        return '\n'.join(lines[:10]) or None

    def check_miter_is_zero(self, miter_aig):
        # The old fraig/sat path had no sequential base/induction obligation.
        return SecResult(SecStatus.UNKNOWN, 0.0, abc_output=(
            "Legacy SAT-only miter checking cannot authorize sequential ODC rewrites; "
            "use an explicit inductive shared-contract miter backend."))


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('baseline_aig', type=Path)
    parser.add_argument('modified_aig', type=Path)
    parser.add_argument('--k-depth', type=int, default=2)
    parser.add_argument('--conflict-limit', type=int, default=30000)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--abc', default='abc')
    args = parser.parse_args()
    result = SecChecker(args.abc, args.conflict_limit, args.timeout).check_equivalence(
        args.baseline_aig, args.modified_aig, args.k_depth)
    print(result)
    if result.status in (SecStatus.ERROR, SecStatus.UNKNOWN):
        print(result.abc_output)
    return 0 if result.is_equivalent else (1 if result.status == SecStatus.NOT_EQUIVALENT else 2)


if __name__ == '__main__':
    raise SystemExit(main())
