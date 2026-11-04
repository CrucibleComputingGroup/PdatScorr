"""Generic, proof-gated equality simplification for sequential designs.

Candidates come from elaborated RTLIL cells, not queue sizes or a hand-cut RTL
variant. A candidate removes high operand bits from one equality. It is accepted
only after both reset-base checking and temporal induction of a supplied explicit
two-design miter. The miter, including assumptions and observations, is immutable.
"""
from __future__ import annotations

import copy
import hashlib
from functools import lru_cache
import json
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import time


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parameter_int(value) -> int:
    return value if isinstance(value, int) else int(value, 2)


def equality_candidates(design: dict, top: str, pattern: str = ".*") -> list[dict]:
    """Enumerate unsigned, equal-width multi-bit $eq cells, narrowest first.

    The optional regex scopes a source cone; it does not specify safe widths.
    No equality output, input, or original state driver is multiply driven.
    """
    validate_hardware(design, top)
    module = design["modules"][top]
    matches = re.compile(pattern)
    result = []
    for name, cell in sorted(module.get("cells", {}).items()):
        if cell["type"] != "$eq":
            continue
        params = cell["parameters"]
        width = parameter_int(params["A_WIDTH"])
        if (width < 2 or width != parameter_int(params["B_WIDTH"])
                or parameter_int(params["A_SIGNED"])
                or parameter_int(params["B_SIGNED"])
                or parameter_int(params["Y_WIDTH"]) != 1):
            continue
        connections = cell["connections"]
        if len(connections["A"]) != width or len(connections["B"]) != width:
            raise ValueError(f"Inconsistent equality cell: {name}")
        names = [wire for wire, net in module.get("netnames", {}).items()
                 if set(net["bits"]) & set(connections["A"] + connections["B"])
                 - {"0", "1", "x", "z"}]
        scope = " ".join([name, str(cell.get("attributes", {}).get("src", "")), *names])
        if not matches.search(scope):
            continue
        for keep in range(1, width):
            result.append({"cell": name, "original_width": width,
                           "retained_low_bits": keep,
                           "operand_nets": names,
                           "source": cell.get("attributes", {}).get("src")})
    return result


def validate_hardware(design: dict, top: str) -> None:
    """Formal premises belong only to the immutable reference environment."""
    if set(design["modules"]) != {top}:
        raise ValueError("Expected exactly one flattened hardware module")
    for cell in design["modules"][top].get("cells", {}).values():
        if cell["type"] in {"$assume", "$assert", "$cover", "$live", "$fair", "$check"}:
            raise ValueError("Hardware input must not contain formal premises/properties")
        if not cell["type"].startswith("$"):
            raise ValueError("Hierarchical or opaque hardware cell is unsupported")


def narrow_equality(design: dict, top: str, candidate: dict) -> dict:
    result = copy.deepcopy(design)
    cell = result["modules"][top]["cells"][candidate["cell"]]
    width = candidate["retained_low_bits"]
    if cell["type"] != "$eq" or not 0 < width < parameter_int(cell["parameters"]["A_WIDTH"]):
        raise ValueError("Candidate does not narrow this equality")
    for port in ("A", "B"):
        cell["connections"][port] = cell["connections"][port][:width]
        cell["parameters"][port + "_WIDTH"] = format(width, "032b")
    return result


def run_command(argv: list[str], logfile: Path, timeout: float) -> dict:
    start = time.monotonic()
    timed_out = False
    with logfile.open("w") as output:
        process = subprocess.Popen(argv, stdout=output, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
    executable = shutil.which(argv[0])
    return {"argv": argv, "returncode": process.returncode,
            "executable": str(Path(executable).resolve()) if executable else None,
            "executable_sha256": digest(Path(executable)) if executable else None,
            "timeout": timed_out, "seconds": time.monotonic() - start,
            "log": str(logfile), "log_sha256": digest(logfile)}


def yosys_path(path: Path) -> str:
    text = str(path.resolve())
    if any(c in text for c in ('"', '\n', '\r', '\\')):
        raise ValueError("Unsupported Yosys path characters")
    return '"' + text + '"'


def checked_yosys(yosys: str, script: str, directory: Path, name: str,
                  timeout: float) -> dict:
    script_path = directory / (name + ".ys")
    script_path.write_text(script)
    result = run_command([yosys, "-Q", "-T", "-s", str(script_path)],
                         directory / (name + ".log"), timeout)
    if result["timeout"] or result["returncode"]:
        raise RuntimeError(f"Yosys failed; see {result['log']}")
    return result


@lru_cache(maxsize=8)
def formal_lower_command(yosys: str) -> str:
    help_text = subprocess.run([yosys, "-Q", "-T", "-p", "help chformal"],
                               capture_output=True, text=True, timeout=10, check=True).stdout
    return "chformal -lower\n" if "-lower" in help_text else ""


def export_design(design: dict, top: str, target: str, output: Path,
                  yosys: str, timeout: float) -> dict:
    validate_hardware(design, top)
    if not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s) for s in (top, target)):
        raise ValueError("Top names must be ordinary Verilog identifiers")
    json_path = output.with_suffix(".json")
    json_path.write_text(json.dumps(design, indent=2) + "\n")
    cell_types = {c["type"] for c in design["modules"][top].get("cells", {}).values()}
    lower = "".join(command + "\n" for kind, command in
                    (("$bwmux", "bwmuxmap"), ("$bmux", "bmuxmap"), ("$demux", "demuxmap"))
                    if kind in cell_types)
    # Keep init attributes: they are part of sequential semantics.
    return checked_yosys(yosys,
        f"read_json {yosys_path(json_path)}\n"
        f"hierarchy -check -top {top}\n"
        + (f"rename {top} {target}\n" if target != top else "")
        + lower
        + f"write_verilog {yosys_path(output)}\n",
        output.parent, output.stem + "_export", timeout)


def proof_passed(result: dict) -> bool:
    if result["timeout"] or result["returncode"] != 0:
        return False
    log = Path(result["log"]).read_text(errors="replace")
    statuses = re.findall(r"Status:\s*(\w+)", log)
    return statuses == ["PASSED"] and not re.search(r"\b(?:ERROR|FAILED)\b", log)


def pair_initial_state(design: dict, top: str) -> dict:
    """Correlate named untouched state between copies only at time zero.

    Both copies start from the same arbitrary RTL state. This neither resets
    payloads the source leaves uninitialized nor assumes equality after time 0.
    Harness instance names are `reference` and `candidate`. Missing or optimized
    state remains unconstrained, which may make proof harder but never stronger.
    """
    module = design["modules"][top]
    initialized = {}
    for net in module["netnames"].values():
        init = net.get("attributes", {}).get("init")
        if init is not None:
            if isinstance(init, int):
                init = format(init, f"0{len(net['bits'])}b")
            for bit, value in zip(net["bits"], reversed(init)):
                if value in ("0", "1"):
                    if bit in initialized and initialized[bit] != value:
                        raise ValueError("Inconsistent initial attributes")
                    initialized[bit] = value
    qbits = set()
    for cell in module["cells"].values():
        if cell["type"] in {"$dff", "$adff", "$sdff", "$dffe", "$adffe",
                            "$sdffe", "$sdffce", "$ff", "$dlatch"}:
            qbits.update(b for b in cell["connections"]["Q"] if isinstance(b, int))
    pairs = {}
    for name, net in module["netnames"].items():
        if not name.startswith("candidate."):
            continue
        original = module["netnames"].get("reference." + name[len("candidate."):])
        if original is None or len(net["bits"]) != len(original["bits"]):
            continue
        for changed, old in zip(net["bits"], original["bits"]):
            if changed not in qbits or old not in qbits or changed == old:
                continue
            if changed in initialized or old in initialized:
                if initialized.get(changed) != initialized.get(old):
                    raise ValueError("Mismatched explicit initial state")
                continue
            if changed in pairs and pairs[changed] != old:
                raise ValueError("Ambiguous initial-state correspondence")
            pairs[changed] = old
    if not pairs:
        return {"paired_state_bits": 0}
    used_bits = [b for net in module["netnames"].values() for b in net["bits"] if isinstance(b, int)]
    used_bits += [b for cell in module["cells"].values() for port in cell["connections"].values()
                 for b in port if isinstance(b, int)]
    initial, same = max(used_bits) + 1, max(used_bits) + 2
    prefix = "$pscorr_initial_state_"
    if any(name.startswith(prefix) for name in module["cells"]):
        raise ValueError("Initial-state pairing already present")
    module["cells"][prefix + "enable"] = {
        "hide_name": 1, "type": "$initstate", "parameters": {}, "attributes": {},
        "port_directions": {"Y": "output"}, "connections": {"Y": [initial]}}
    module["cells"][prefix + "equal"] = {
        "hide_name": 1, "type": "$eq", "attributes": {},
        "parameters": {"A_SIGNED": "0" * 32, "B_SIGNED": "0" * 32,
                       "A_WIDTH": format(len(pairs), "032b"),
                       "B_WIDTH": format(len(pairs), "032b"),
                       "Y_WIDTH": format(1, "032b")},
        "port_directions": {"A": "input", "B": "input", "Y": "output"},
        "connections": {"A": list(pairs.values()), "B": list(pairs), "Y": [same]}}
    module["cells"][prefix + "assume"] = {
        "hide_name": 1, "type": "$assume", "parameters": {}, "attributes": {},
        "port_directions": {"A": "input", "EN": "input"},
        "connections": {"A": [same], "EN": [initial]}}
    # This is an additional proof obligation, NOT an assumption: unchanged
    # state correspondence makes induction practical without hiding a mismatch.
    # Equality narrowing preserves the representation of every surviving FF.
    module["cells"][prefix + "invariant"] = {
        "hide_name": 1, "type": "$assert", "parameters": {}, "attributes": {},
        "port_directions": {"A": "input", "EN": "input"},
        "connections": {"A": [same], "EN": ["1"]}}
    return {"paired_state_bits": len(pairs), "scope": "matching named FF Q bits at $initstate only",
            "induction_helper": "assert (never assume) continuing state correspondence",
            "pairs": [[a, b] for a, b in sorted(pairs.items())]}


def prove_pair(reference: Path, candidate: Path, harness: Path, top: str,
               directory: Path, *, yosys: str, smtbmc: str, solver: str,
               depth: int, timeout: float, engine: str = "induction",
               abc: str = "abc") -> dict:
    """A bounded pass alone can never return proven=True."""
    directory.mkdir()
    if depth < 2 or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", top) or engine not in ("induction", "pdr"):
        raise ValueError("Invalid proof top or induction depth")
    smt = directory / "miter.smt2"
    result = {"proven": False, "method": "reset-base-and-k-induction" if engine == "induction" else "abc-pdr-shared-miter",
              "depth": depth, "reference_sha256": digest(reference),
              "candidate_sha256": digest(candidate), "harness_sha256": digest(harness),
              "implementation_sha256": digest(Path(__file__))}
    try:
        intermediate = directory / "miter.json"
        result["elaboration"] = checked_yosys(yosys,
            f"read_verilog -formal -sv {yosys_path(reference)} {yosys_path(candidate)} {yosys_path(harness)}\n"
            f"prep -top {top} -flatten\ncheck -assert\n"
            + formal_lower_command(yosys)
            # Fail if all observation assertions have disappeared.
            + "select -assert-min 1 t:$assert\nselect *\n"
            "async2sync\ndffunmap\n"
            f"write_json {yosys_path(intermediate)}\n",
            directory, "prepare", timeout)
        miter_design = json.loads(intermediate.read_text())
        cells = miter_design["modules"][top]["cells"]
        result["property_counts"] = {kind: sum(cell["type"] == "$" + kind for cell in cells.values())
                                     for kind in ("assert", "assume", "cover")}
        result["initial_state"] = pair_initial_state(miter_design, top)
        intermediate.write_text(json.dumps(miter_design) + "\n")
        if engine == "pdr":
            aig = directory / "miter.aig"
            result["aig_export"] = checked_yosys(yosys,
                f"read_json {yosys_path(intermediate)}\ncheck -assert\n"
                "chformal -cover -remove\nformalff -clk2ff\nsetundef -anyseq\nopt -keepdc\ntechmap\nopt -keepdc\n"
                # ABC's BLIF extraction otherwise concretizes remaining x bits
                # to zero. Preserve them as independent symbolic choices.
                "setundef -anyseq\n"
                "abc -g AND\naigmap\n"
                f"write_aiger -zinit -symbols {yosys_path(aig)}\n",
                directory, "aig_export", timeout)
            with aig.open("rb") as stream:
                header = stream.readline().decode("ascii").split()
            if (header[0] != "aig" or len(header) < 7 or int(header[4]) != 0
                    or int(header[6]) < 1 or any(int(x) for x in header[8:])):
                raise ValueError("PDR expects safety assertions, no ordinary outputs/liveness")
            result["aig_sha256"] = digest(aig)
            result["aig_bad_properties"] = int(header[6])
            result["aig_constraints"] = int(header[7]) if len(header) > 7 else 0
            # ABC's AIGER reader recognizes constraints. fold creates a sticky
            # violation flag; orpos then combines all safety properties. zinit
            # preserves arbitrary original state through new initial inputs.
            if any(c in str(aig.resolve()) for c in (';', '"', '\\', '\n', '\r')):
                raise ValueError("Unsupported ABC path characters")
            command = (f'read_aiger "{aig.resolve()}"; fold; orpos; '
                       f'pdr -T {max(1, int(timeout))} -v')
            result["pdr"] = run_command([abc, "-c", command], directory / "pdr.log", timeout + 5)
            log = (directory / "pdr.log").read_text(errors="replace")
            result["proven"] = (result["pdr"]["returncode"] == 0
                and not result["pdr"]["timeout"]
                and len(re.findall(r"(?m)^Property proved\.", log)) == 1
                and not re.search(r"\b(error|failed|undecided|disproved|timed out|time limit|was asserted)\b", log, re.I))
        else:
            result["smt_export"] = checked_yosys(yosys,
                f"read_json {yosys_path(intermediate)}\ncheck -assert\n"
                f"write_smt2 -wires {yosys_path(smt)}\n", directory, "smt_export", timeout)
            result["smt_sha256"] = digest(smt)
            args = [smtbmc, "-s", solver, "-t", str(depth), "--noprogress"]
            result["base"] = run_command(args + ["--dump-vcd", str(directory / "counterexample.vcd"), str(smt)],
                                         directory / "base.log", timeout)
            if proof_passed(result["base"]):
                result["induction"] = run_command(args + ["-i", str(smt)],
                                                  directory / "induction.log", timeout)
                result["proven"] = proof_passed(result["induction"])
    except (RuntimeError, OSError, ValueError) as error:
        result["error"] = str(error)
    for name, path in (("reference", reference), ("candidate", candidate), ("harness", harness),
                       ("implementation", Path(__file__))):
        if digest(path) != result[name + "_sha256"]:
            result["proven"] = False
            result["error"] = f"{name} changed during proof"
    (directory / "proof.json").write_text(json.dumps(result, indent=2) + "\n")
    return result
