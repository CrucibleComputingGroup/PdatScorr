"""Guard discovery is structural; guarded equalities remain proof obligations."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
HELPERS = ROOT / "experiments/bounded_dynamic/len5/phase_sharing"
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location("guard_invariants", HELPERS / "guard_invariants.py")
guards = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guards)
from odc.temporal import checked_yosys, proof_passed, run_command

MODERN = ROOT.parents[2] / "tools/oss-cad-suite-20261104/oss-cad-suite/bin/yosys"
YOSYS = str(MODERN) if MODERN.exists() else shutil.which("yosys")


def fixture():
    def ff(q):
        return {"type": "$adff", "parameters": {"WIDTH": len(q), "ARST_VALUE": "0" * len(q)},
                "connections": {"Q": q, "D": q, "CLK": [2], "ARST": [3]},
                "port_directions": {"Q": "output", "D": "input", "CLK": "input", "ARST": "input"}}
    def eq(q, value, y):
        return {"type": "$eq", "parameters": {"A_WIDTH": len(q), "B_WIDTH": len(value), "Y_WIDTH": 1},
                "connections": {"A": q, "B": value, "Y": [y]},
                "port_directions": {"A": "input", "B": "input", "Y": "output"}}
    cells = {"near": ff([10, 11]), "other": ff([12, 13]),
             "one": eq([10, 11], ["1", "0"], 20),
             "two": eq([10, 11], ["0", "1"], 21),
             "duplicate_one": eq([10, 11], ["1", "0"], 22),
             "unrelated": eq([12, 13], ["1", "0"], 23),
             "undefined": eq([10, 11], ["x", "0"], 24),
             "payload_a": ff([30, 31, 32, 33]), "payload_b": ff([34, 35, 36, 37]),
             "shared": ff([38, 39, 40, 41])}
    model = {"modules": {"M": {"cells": cells, "ports": {}, "netnames": {}}}}
    bank = {"reference_a_enable": [20], "reference_b_enable": [21],
            "reference_a_q": [30, 31, 32, 33], "reference_b_q": [34, 35, 36, 37],
            "candidate_shared_q": [38, 39, 40, 41]}
    return model, bank


def test_discovery_uses_existing_native_control_not_names_or_payload_width():
    design, bank = fixture()
    discovery = guards.discover_guards(design, "M", bank, max_control_width=2)
    assert discovery["selected_controls"] == ["near"]
    assert len(discovery["candidates"]) == 4  # two distinct predicates x two banks
    assert {c["control_cell"] for c in discovery["candidates"]} == {"near"}
    assert all(c["cell"] not in ("unrelated", "undefined") for c in discovery["candidates"])
    assert discovery["assumptions_added"] == 0


def test_discovery_does_not_cross_sequential_boundaries():
    design, bank = fixture()
    design["modules"]["M"]["cells"]["near"]["connections"]["D"] = [12, 13]
    found = guards.discover_guards(design, "M", bank, max_control_width=2)
    assert len(found["ranked_controls"]) == 1


def test_guard_instrumentation_preserves_hardware_and_premises():
    design, bank = fixture()
    found = guards.discover_guards(design, "M", bank)["candidates"]
    original = copy.deepcopy(design)
    changed = guards.add_guard_assertions(design, "M", found)
    assert design == original
    for name, cell in original["modules"]["M"]["cells"].items():
        assert changed["modules"]["M"]["cells"][name] == cell
    added = [c for n, c in changed["modules"]["M"]["cells"].items() if n not in original["modules"]["M"]["cells"]]
    assert {c["type"] for c in added} == {"$eq", "$assert"}
    assert sum(c["type"] == "$assert" for c in added) == 4


def test_failure_parser_rejects_unrelated_failures():
    assert guards.rejected_guards("Assert failed in M: $pscorr_guard_000_a (guard_candidate:guard_000_a)", {"guard_000_a"}) == {"guard_000_a"}
    with pytest.raises(ValueError, match="attributed"):
        guards.rejected_guards("Assert failed in M: functional_output", {"guard_000_a"})


def test_guard_allocator_preserves_unused_port_and_alias_bit_ids():
    design, bank = fixture()
    design["modules"]["M"]["ports"]["unused"] = {"direction": "input", "bits": [900]}
    design["modules"]["M"]["netnames"]["unused_alias"] = {"bits": [950]}
    found = guards.discover_guards(design, "M", bank)["candidates"]
    changed = guards.add_guard_assertions(design, "M", found)
    new_equalities = [c for n, c in changed["modules"]["M"]["cells"].items()
                      if n.startswith("$pscorr_guard_equal_")]
    assert all(c["connections"]["Y"][0] > 950 for c in new_equalities)
    with pytest.raises(ValueError, match="Duplicate guard"):
        guards.add_guard_assertions(design, "M", [found[0], found[0]])


def test_nonpositive_search_bounds_rejected():
    design, bank = fixture()
    with pytest.raises(ValueError, match="positive"):
        guards.discover_guards(design, "M", bank, control_limit=0)


@pytest.mark.skipif(not YOSYS or not shutil.which("z3"), reason="Yosys/Z3 required")
def test_real_bmc_discards_false_guards_then_joint_induction_proves(tmp_path):
    source = tmp_path / "source.sv"
    source.write_text('''module M(input clk,rst_ni,advance,input [3:0] da,db);
      reg [1:0] control;
      reg [3:0] a,b,shared;
      wire ena=(control==0)&&advance, enb=(control==2)&&advance;
      wire [3:0] original_out=(control==1)?a:((control==3)?b:4'b0);
      wire [3:0] changed_out=((control==1)||(control==3))?shared:4'b0;
      always @(posedge clk or negedge rst_ni) begin
        if(!rst_ni) begin control<=0; a<=0; b<=0; shared<=0; end
        else begin
          if(advance) control<=control+1;
          if(ena) begin a<=da; shared<=da; end
          if(enb) begin b<=db; shared<=db; end
        end
      end
      always @* begin if($initstate) assume(!rst_ni); assert(original_out==changed_out); end
    endmodule''')
    native = tmp_path / "native.json"
    checked_yosys(YOSYS, f'read_verilog -formal -sv "{source}"\nprep -top M\nopt_dff\nwrite_json "{native}"\n', tmp_path, "prepare", 20)
    design = json.loads(native.read_text())
    nets = design["modules"]["M"]["netnames"]
    bank = {"reference_a_enable": nets["ena"]["bits"], "reference_b_enable": nets["enb"]["bits"],
            "reference_a_q": nets["a"]["bits"], "reference_b_q": nets["b"]["bits"],
            "candidate_shared_q": nets["shared"]["bits"]}
    discovery = guards.discover_guards(design, "M", bank)
    candidates = discovery["candidates"]
    assert len(candidates) == 8
    smt, _ = guards.export_smt(guards.add_guard_assertions(design, "M", candidates, guard_only=True), "M", tmp_path / "screen", YOSYS)
    smtbmc = str(Path(YOSYS).with_name("yosys-smtbmc"))
    result = run_command([smtbmc, "-s", "z3", "-t", "8", "--noprogress", "--keep-going", str(smt)], tmp_path / "screen/bmc.log", 20)
    rejected = guards.rejected_guards(Path(result["log"]).read_text(), {g["id"] for g in candidates})
    assert len(rejected) == 4
    survivors = [g for g in candidates if g["id"] not in rejected]
    smt, meta = guards.export_smt(guards.add_guard_assertions(design, "M", survivors), "M", tmp_path / "joint", YOSYS)
    assert meta["property_counts"] == {"assert": 5, "assume": 1}
    cmd = [smtbmc, "-s", "z3", "-t", "3", "--noprogress"]
    base = run_command(cmd + [str(smt)], tmp_path / "joint/base.log", 20)
    step = run_command(cmd + ["-i", str(smt)], tmp_path / "joint/step.log", 20)
    assert proof_passed(base) and proof_passed(step)
