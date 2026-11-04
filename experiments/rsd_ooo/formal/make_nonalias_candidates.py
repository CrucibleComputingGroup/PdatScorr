#!/usr/bin/env python3
"""Generate isolated RSD LSQ candidates; never alter the source checkout."""
import argparse
import hashlib
import json
from pathlib import Path

from prove_nonalias import HERE, SOURCE_HASHES


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path, default=HERE.parent / "rsd/Processor/Src")
    parser.add_argument("--output", type=Path, default=HERE / "generated")
    args = parser.parse_args()
    summary = json.loads((HERE / "results/proof_summary.json").read_text())
    if summary["status"] != "passed":
        raise RuntimeError("Run prove_nonalias.py successfully before generating candidates")
    actual_summary_path = HERE / "results/actual_lsq/summary.json"
    actual_summary = json.loads(actual_summary_path.read_text())
    if actual_summary["status"] != "passed":
        raise RuntimeError("Run prove_actual_lsq.py successfully before generating candidates")
    replacements = {
        "LoadQueue.sv": (
            """addrMatch[si][lqe] =
                    loadQueue[lqe].finished &&
                    loadQueue[lqe].regValid &&
                    loadQueue[lqe].address == executedStoreAddr[si] &&
                    (loadQueue[lqe].wordRE & executedStoreWordWE[si]) != '0;""",
            """// Pscorr candidate under the all-executed-operation physical-region contract.
                // Stored load addresses cannot equal an active store address.
                // Keep the separate same-cycle conflict loop unchanged.
                addrMatch[si][lqe] = FALSE;"""),
        "StoreQueue.sv": (
            """addrMatch[i][j] =
                    storeQueue[j].finished &&
                    port.executedLoadMemMapType[i] != MMT_ILLEGAL && 
                    storeQueue[j].address == LSQ_ToBlockAddr(port.executedLoadAddr[i]) &&
                    ((storeQueue[j].wordWE & executedLoadWordRE[i]) != '0) &&
                    ((storeQueue[j].byteWE & executedLoadByteRE[i]) != '0);""",
            """// Pscorr candidate under the all-executed-operation physical-region contract.
                // Forwarding is disabled; unselected data/miss outputs are ODCs.
                // Retain store commitment, queue admission, and recovery logic.
                addrMatch[i][j] = FALSE;"""),
    }
    args.output.mkdir(parents=True, exist_ok=True)
    manifest = {"contract": summary["contract"], "proof_scope": actual_summary["scope"],
                "actual_rtl_proof": str(actual_summary_path.resolve()),
                "supporting_extracted_relation": summary["scope"],
                "observation_relation": summary["observation_relation"], "files": []}
    for filename, (old, new) in replacements.items():
        relative = "LoadStoreUnit/" + filename
        source = args.src / relative
        original = source.read_bytes()
        if hashlib.sha256(original).hexdigest() != SOURCE_HASHES[relative]:
            raise RuntimeError(f"Source hash differs: {source}")
        text = original.decode()
        if text.count(old) != 1:
            raise RuntimeError(f"Expected exactly one replacement in {source}")
        candidate = text.replace(old, new)
        destination = args.output / filename
        destination.write_text(candidate)
        manifest["files"].append({"source": str(source.resolve()), "candidate": str(destination.resolve()),
                                   "source_sha256": hashlib.sha256(original).hexdigest(),
                                   "candidate_sha256": hashlib.sha256(candidate.encode()).hexdigest()})
    (args.output / "candidate_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Generated {len(manifest['files'])} candidate modules in {args.output}")


if __name__ == "__main__":
    main()
