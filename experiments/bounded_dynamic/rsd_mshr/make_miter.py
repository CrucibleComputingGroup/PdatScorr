#!/usr/bin/env python3
"""Generate an immutable, all-defined-output miter from baseline port metadata."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--spacing", type=int, default=3)
    parser.add_argument("--latency", type=int, default=5)
    parser.add_argument("--unordered", action="store_true")
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit("Refusing to overwrite a miter")
    if args.spacing < 2 or args.latency < 2:
        raise SystemExit("This monitor requires bounds of at least two cycles")
    ports = json.loads(args.baseline.read_text())["modules"]["MshrObserved"]["ports"]
    inputs, outputs, reference, candidate = [], [], [], []
    observed = []
    for name, port in ports.items():
        width = len(port["bits"])
        size = "" if width == 1 else f"[{width-1}:0] "
        if port["direction"] == "input":
            inputs.append(f"input wire {size}{name}")
            reference.append(f".{name}({name})")
            candidate.append(f".{name}({name})")
        elif port["direction"] == "output":
            outputs.append(f"wire {size}ref_{name}, cand_{name};")
            reference.append(f".{name}(ref_{name})")
            candidate.append(f".{name}(cand_{name})")
            observed.append(f"  assert(ref_{name} == cand_{name});")
        else:
            raise ValueError("Inout port unsupported")
    lines = ["// Baseline JSON SHA256: " + hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
             "// Both copies share all inputs; all defined functional outputs are compared.",
             "module TemporalMiter (" + ",\n".join(inputs) + ");", *outputs,
             "MshrObserved reference(" + ",\n".join(reference) + ");",
             "MshrCandidate candidate(" + ",\n".join(candidate) + ");",
             f"ReadServiceContract #(.MIN_SPACING({args.spacing}),.MAX_LATENCY({args.latency}),"
             f".ORDERED({0 if args.unordered else 1})) service(",
             "  .clk(clk),.rst(rst),.read_accept(ref_read_accept),.allocated_id(ref_allocated_id),",
             "  .response_valid(response_valid),.response_id(response_id));",
             "always @* begin", *observed, "end", "endmodule",
             Path(__file__).with_name("ReadServiceContract.sv").read_text()]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines).rstrip() + "\n")


if __name__ == "__main__":
    main()
