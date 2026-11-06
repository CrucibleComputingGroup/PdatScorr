"""Soundness tests for the ternary reachability checker and constant substitution.

Each tsim case is a small binary AIGER model whose reachable states are known by
hand. The cases cover the ways an unsound checker would over-claim constants:
a latch that changes only after the simulated frames, a latch reachable only
after a later reset, an uninitialized latch, free inputs, and vacuous or
input-dependent constraints.
"""
from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "experiments/bounded_dynamic/len5/ternary_reach"


def varint(x: int) -> bytes:
    out = bytearray()
    while x & ~0x7F:
        out.append((x & 0x7F) | 0x80)
        x >>= 7
    out.append(x)
    return bytes(out)


class Aig:
    """Binary AIGER writer. Input 0 is the active-low reset."""

    def __init__(self, inputs: int, latches: int):
        self.I, self.L = inputs, latches
        self.ands: list[tuple[int, int, int]] = []
        self.next = [None] * latches
        self.init: list = [0] * latches
        self.outs: list[int] = []
        self.bads: list[int] = []
        self.cons: list[int] = []

    def inp(self, k: int) -> int:
        return 2 * (1 + k)

    def latch(self, k: int) -> int:
        return 2 * (1 + self.I + k)

    def AND(self, a: int, b: int) -> int:
        lhs = 2 * (1 + self.I + self.L + len(self.ands))
        self.ands.append((lhs, max(a, b), min(a, b)))
        return lhs

    def OR(self, a: int, b: int) -> int:
        return self.AND(a ^ 1, b ^ 1) ^ 1

    def MUX(self, s: int, a: int, b: int) -> int:
        return self.OR(self.AND(s, a), self.AND(s ^ 1, b))

    def write(self, path: Path) -> Path:
        m = self.I + self.L + len(self.ands)
        text = f"aig {m} {self.I} {self.L} {len(self.outs)} {len(self.ands)} {len(self.bads)} {len(self.cons)}\n"
        data = bytearray(text.encode())
        for k in range(self.L):
            init = self.latch(k) if self.init[k] == "x" else self.init[k]
            data += f"{self.next[k]} {init}\n".encode()
        for lit in self.outs + self.bads + self.cons:
            data += f"{lit}\n".encode()
        for lhs, r0, r1 in self.ands:
            data += varint(lhs - r0) + varint(r0 - r1)
        path.write_bytes(bytes(data))
        return path


@pytest.fixture(scope="module")
def tsim(tmp_path_factory) -> Path:
    gcc = shutil.which("gcc", path="/usr/bin:/bin")
    if gcc is None:
        pytest.skip("gcc needed to build tsim")
    out = tmp_path_factory.mktemp("tsim") / "tsim"
    subprocess.run([gcc, "-O2", "-std=c11", "-Wall", "-Wextra", "-Werror", "-o", str(out), str(HERE / "tsim.c")],
                   check=True, env=dict(os.environ, PATH="/usr/bin:/bin"))
    return out


def run(tsim: Path, aig: Aig, tmp_path: Path, frames: int = 32, period: int = 8) -> dict:
    model = aig.write(tmp_path / "m.aig")
    proc = subprocess.run([str(tsim), str(model), "0", str(frames), str(period), str(tmp_path / "t")],
                          capture_output=True, text=True)
    result = dict(line.split(" ", 1) for line in (tmp_path / "t.result.txt").read_text().splitlines())
    result["outjoin"] = list((tmp_path / "t.outjoin.bin").read_bytes())
    result["returncode"] = proc.returncode
    assert proc.returncode == (0 if result["invariant_ok"] == "1" else 1)
    return result


def test_held_reset_value_is_constant(tsim, tmp_path):
    a = Aig(1, 1)
    a.next[0] = a.AND(a.inp(0), a.latch(0))
    a.outs = [a.latch(0)]
    r = run(tsim, a, tmp_path)
    assert r["invariant_ok"] == "1" and r["outjoin"] == [0]


def test_toggle_and_free_input_vary(tsim, tmp_path):
    a = Aig(2, 2)
    a.next[0] = a.AND(a.inp(0), a.latch(0) ^ 1)
    a.next[1] = a.AND(a.inp(0), a.inp(1))
    a.outs = [a.latch(0), a.latch(1)]
    r = run(tsim, a, tmp_path)
    assert r["invariant_ok"] == "1" and r["outjoin"] == [2, 2]


def test_uninitialized_latch_is_never_constant(tsim, tmp_path):
    a = Aig(1, 1)
    a.init[0] = "x"
    a.next[0] = 0
    a.outs = [a.latch(0)]
    r = run(tsim, a, tmp_path)
    assert r["invariant_ok"] == "1" and r["outjoin"] == [2]


def counter_with_sticky(width: int) -> Aig:
    """Reset counter (width bits) and a sticky bit set when the counter is all ones."""
    a = Aig(1, width + 1)
    carry = 1
    for k in range(width):
        bit = a.latch(k)
        a.next[k] = a.AND(a.inp(0), a.OR(a.AND(bit, carry ^ 1), a.AND(bit ^ 1, carry)))
        carry = a.AND(carry, bit)
    sticky = a.latch(width)
    a.next[width] = a.AND(a.inp(0), a.OR(sticky, carry))
    a.outs = [a.latch(k) for k in range(width + 1)]
    return a


def test_late_change_is_not_claimed_constant(tsim, tmp_path):
    """The sticky bit is 0 in all four simulated frames and first rises in frame 9."""
    r = run(tsim, counter_with_sticky(3), tmp_path, frames=4, period=2)
    assert r["invariant_ok"] == "1" and r["outjoin"][-1] == 2


def test_exact_lasso_after_wrap(tsim, tmp_path):
    r = run(tsim, counter_with_sticky(3), tmp_path, frames=40, period=16)
    assert r["invariant_ok"] == "1" and r["period"] == "8" and r["period_initial_diff"] == "0"
    assert r["outjoin"] == [2, 2, 2, 2]


def test_unclosed_widening_rejects(tsim, tmp_path):
    """A 300-stage shift chain needs more than the 256 permitted widening rounds."""
    a = Aig(1, 301)
    a.next[0] = a.AND(a.inp(0), a.latch(0) ^ 1)
    for k in range(1, 301):
        a.next[k] = a.AND(a.inp(0), a.latch(k - 1))
    a.outs = [a.latch(300)]
    r = run(tsim, a, tmp_path, frames=4, period=1)
    assert r["closed"] == "0" and r["invariant_ok"] == "0"


def test_state_reachable_only_after_rereset_rejects(tsim, tmp_path):
    """B copies A only under reset; A becomes 1 after the first frame."""
    a = Aig(1, 2)
    a.next[0] = 1
    a.next[1] = a.MUX(a.inp(0), a.latch(1), a.latch(0))
    a.outs = [a.latch(1)]
    r = run(tsim, a, tmp_path)
    assert r["outjoin"] == [0]  # B is 0 on the main trajectory and its closure
    assert int(r["rereset_uncovered"]) > 0 and r["invariant_ok"] == "0"


def test_reachable_bad_rejects(tsim, tmp_path):
    a = counter_with_sticky(2)
    a.bads = [a.latch(2)]
    r = run(tsim, a, tmp_path)
    assert int(r["property_failures"]) > 0 and r["invariant_ok"] == "0"


def test_state_constraint_masks_bad(tsim, tmp_path):
    a = counter_with_sticky(2)
    a.bads = [a.latch(2)]
    a.cons = [a.latch(2) ^ 1]
    r = run(tsim, a, tmp_path)
    assert r["property_failures"] == "0" and r["invariant_ok"] == "1"


def test_input_constraint_does_not_refine(tsim, tmp_path):
    """Constraints over free inputs are X in ternary simulation; the check stays conservative."""
    a = Aig(2, 1)
    a.next[0] = 0
    a.bads = [a.inp(1)]
    a.cons = [a.inp(1) ^ 1]
    a.outs = [a.latch(0)]
    r = run(tsim, a, tmp_path)
    assert int(r["property_failures"]) > 0 and r["invariant_ok"] == "0"


def test_vacuous_constraint_rejects(tsim, tmp_path):
    a = Aig(1, 1)
    a.next[0] = 0
    a.outs = [a.latch(0)]
    a.cons = [0]
    r = run(tsim, a, tmp_path)
    assert r["outputs_never"] == "1" and r["invariant_ok"] == "0"


# Constant substitution ------------------------------------------------------

def design() -> dict:
    ff = {"$aldff": {"CLK": "input", "ALOAD": "input", "AD": "input", "D": "input", "Q": "output"},
          "$dffe": {"CLK": "input", "EN": "input", "D": "input", "Q": "output"}}
    return {"modules": {"datapath": {
        "ports": {"clk": {"direction": "input", "bits": [2]}, "rst": {"direction": "input", "bits": [3]},
                  "d": {"direction": "input", "bits": [4, 5]}, "y": {"direction": "output", "bits": [6, 7]},
                  "q": {"direction": "output", "bits": [8, 9]}},
        "cells": {
            "r": {"type": "$aldff", "port_directions": ff["$aldff"],
                  "connections": {"CLK": [2], "ALOAD": [3], "AD": ["0", "1"], "D": [4, 5], "Q": [8, 9]}},
            "n": {"type": "$dffe", "port_directions": ff["$dffe"],
                  "connections": {"CLK": [2], "EN": [3], "D": [8, 9], "Q": [10, 11]}},
            "g": {"type": "$and", "port_directions": {"A": "input", "B": "input", "Y": "output"},
                  "connections": {"A": [8, 9], "B": [10, 11], "Y": [6, 7]}}},
        "netnames": {"q": {"bits": [8, 9]}, "y": {"bits": [6, 7]}, "nq": {"bits": [10, 11]}}}}}


def substitute(tmp_path: Path, des: dict, *constant_sets: list[dict], status: str = "certified",
               flags: tuple[str, ...] = (), witness_status: str = "passed") -> subprocess.CompletedProcess:
    tmp_path.mkdir(parents=True, exist_ok=True)
    path = tmp_path / "design.json"
    path.write_text(json.dumps(des))
    sha = hashlib.sha256(path.read_bytes()).hexdigest()
    files = []
    for i, constants in enumerate(constant_sets):
        f = tmp_path / f"constants{i}.json"
        f.write_text(json.dumps({"status": status, "design_sha256": sha, "gap": i + 1, "model_aig_sha256": str(i),
                                 "witness_status": witness_status, "constants": constants}))
        files.append(str(f))
    return subprocess.run([sys.executable, str(HERE / "substitute.py"), "--design", str(path), "--constants",
                           *files, "--output", str(tmp_path / "out"), *flags], capture_output=True, text=True)


def test_substitution_rewires_consumers_only(tmp_path):
    proc = substitute(tmp_path, design(), [{"cell": "r", "bit": 0, "net": 8, "value": 0}])
    assert proc.returncode == 0, proc.stderr
    result = json.loads((tmp_path / "out/design.json").read_text())["modules"]["datapath"]
    original = design()["modules"]["datapath"]
    assert result["cells"]["r"] == original["cells"]["r"]
    assert result["cells"]["n"]["connections"]["D"] == ["0", 9]
    assert result["cells"]["g"]["connections"]["A"] == ["0", 9]
    assert result["ports"]["q"]["bits"] == ["0", 9] == result["netnames"]["q"]["bits"]
    summary = json.loads((tmp_path / "out/summary.json").read_text())
    assert summary["applied_constant_bits"] == 1
    assert summary["rewired_connections"] == {"$and.A": 1, "$dffe.D": 1, "module_output.q": 1}


def test_only_common_constants_are_applied(tmp_path):
    proc = substitute(tmp_path, design(),
                      [{"cell": "r", "bit": 0, "net": 8, "value": 0}, {"cell": "r", "bit": 1, "net": 9, "value": 1}],
                      [{"cell": "r", "bit": 1, "net": 9, "value": 1}])
    assert proc.returncode == 0, proc.stderr
    applied = json.loads((tmp_path / "out/applied_constants.json").read_text())
    assert applied == [{"cell": "r", "bit": 1, "net": 9, "value": 1}]


@pytest.mark.parametrize("constant", [
    {"cell": "r", "bit": 1, "net": 9, "value": 0},    # differs from the reset value
    {"cell": "n", "bit": 0, "net": 10, "value": 0},   # flip-flop without reset
    {"cell": "r", "bit": 0, "net": 9, "value": 0},    # net is not that Q bit
    {"cell": "g", "bit": 0, "net": 6, "value": 0},    # not a flip-flop
])
def test_invalid_constants_rejected(tmp_path, constant):
    proc = substitute(tmp_path, design(), [constant])
    assert proc.returncode != 0 and "ValueError" in proc.stderr


def test_simulation_bound_needs_flag_and_is_marked(tmp_path):
    constant = {"cell": "r", "bit": 0, "net": 8, "value": 0}
    proc = substitute(tmp_path, design(), [constant], status="simulation_bound_not_certified")
    assert proc.returncode != 0 and "ValueError" in proc.stderr
    proc = substitute(tmp_path / "a", design(), [constant], flags=("--simulation-bound",))
    assert proc.returncode != 0 and "ValueError" in proc.stderr   # certified input is not a bound
    proc = substitute(tmp_path / "b", design(), [constant], [constant], status="simulation_bound_not_certified",
                      flags=("--simulation-bound",))
    assert proc.returncode != 0 and "applied alone" in proc.stderr
    proc = substitute(tmp_path / "d", design(), [constant], status="simulation_bound_not_certified",
                      flags=("--simulation-bound",), witness_status="failed")
    assert proc.returncode != 0 and "passed witness run" in proc.stderr
    proc = substitute(tmp_path / "c", design(), [constant], status="simulation_bound_not_certified",
                      flags=("--simulation-bound",))
    assert proc.returncode == 0, proc.stderr
    assert json.loads((tmp_path / "c/out/summary.json").read_text())["status"] == "substituted_simulation_bound"


def test_constant_reaching_reset_control_rejected(tmp_path):
    des = design()
    cells = des["modules"]["datapath"]["cells"]
    cells["n"] = {"type": "$aldff", "port_directions": copy.deepcopy(cells["r"]["port_directions"]),
                  "connections": {"CLK": [2], "ALOAD": [8], "AD": ["0", "0"], "D": [8, 9], "Q": [10, 11]}}
    proc = substitute(tmp_path, des, [{"cell": "r", "bit": 0, "net": 8, "value": 0}])
    assert proc.returncode != 0 and "clock/reset/load" in proc.stderr


# Randomized-timing witness platform -------------------------------------------

def timing_witness():
    sys.path.insert(0, str(HERE))
    import timing_witness as tw
    return tw


def test_randomized_platform_replaces_both_timing_mechanisms():
    tw = timing_witness()
    formal = ("module AdmissionScreen(input wire clk_i, rst_ni,\n  input wire [2:0] invalid_code_nonzero, "
              + tw.FAULT_DATA_PORT + "  output wire obs_load);\n  reg [0:0] gap_left;\n"
              + tw.FIXED_GATE + tw.FIXED_SERVICE + "endmodule\n")
    text = tw.randomized_platform(formal)
    assert "gap_left == 0" not in text and "lv <=" not in text and tw.RANDOM_SERVICE in text
    assert "  wire gate_open = fetch_gate;" in text
    assert "  input wire fetch_gate, load_gnt, load_reply, store_gnt, store_reply,\n" in text
    with pytest.raises(ValueError):
        tw.randomized_platform(formal.replace(tw.FIXED_SERVICE, ""))


def test_timing_testbench_drives_inputs_and_counts_accepted_requests():
    tw = timing_witness()
    from cosim import fill, hex_vector
    tb = fill(tw.timing_testbench(), W=4, K=2, NV=1, THRESHOLD=0, CMASK=hex_vector([0] * 4), CVAL=hex_vector([0] * 4),
              WMASK=hex_vector([1] * 4), WVAL=hex_vector([0] * 4), IMG_BASE="1000", IMG_WORDS=1, INSTANCES="", CHECKS="")
    start = tb.index("Platform_orig orig(")
    instance = tb[start:tb.index(");", start)]
    assert all(f".{n}({n})" in instance for n in tw.TIMING_INPUTS)
    assert "if (o_load && orig.data_load_gnt_i) loads++;" in tb
    assert "if (o_store && orig.data_store_gnt_i) begin" in tb
    assert "seen = seen | ((o_ffq ^ WVAL) & WMASK);" in tb and '$display("WITNESS %h", seen);' in tb


SERVICE_TB = r"""
module svc(input wire clk_i, rst_ni, data_load_req_o, data_load_rready_o, data_store_req_o, data_store_rready_o,
  input wire [3:0] data_load_tag_o, data_store_tag_o, input wire [63:0] load_value,
  input wire load_gnt, load_reply, store_gnt, store_reply,
  output wire data_load_gnt_i, data_load_rvalid_i, data_store_gnt_i, data_store_rvalid_i,
  output wire [3:0] data_load_tag_i, data_store_tag_i, output wire [63:0] data_load_rdata_i);
@SERVICE@
endmodule

module tb;
  logic clk = 0, rst_ni = 0, lreq = 0, sreq = 0, lrr = 1, srr = 1, lg = 0, lr = 0, sg = 0, sr = 0;
  logic [3:0] ltag = 0, stag = 0;
  logic [63:0] lval = 0;
  wire lgnt, lvalid, sgnt, svalid;
  wire [3:0] ltag_i, stag_i;
  wire [63:0] ldata;
  svc dut(.clk_i(clk), .rst_ni(rst_ni), .data_load_req_o(lreq), .data_load_rready_o(lrr), .data_store_req_o(sreq),
          .data_store_rready_o(srr), .data_load_tag_o(ltag), .data_store_tag_o(stag), .load_value(lval),
          .load_gnt(lg), .load_reply(lr), .store_gnt(sg), .store_reply(sr), .data_load_gnt_i(lgnt),
          .data_load_rvalid_i(lvalid), .data_store_gnt_i(sgnt), .data_store_rvalid_i(svalid),
          .data_load_tag_i(ltag_i), .data_store_tag_i(stag_i), .data_load_rdata_i(ldata));
  // Reference model: requests are held until granted; replies leave in grant order.
  logic [67:0] lq [$];
  logic [3:0] sq [$];
  logic [67:0] lprev;
  logic [3:0] sprev;
  logic lheld = 0, sheld = 0, lfree = 1, sfree = 1;
  longint unsigned lpush = 0, lpop = 0, spush = 0, spop = 0, full = 0, errors = 0;
  initial begin
    for (int cyc = 0; cyc < 200000; cyc++) begin
      rst_ni = !(cyc < 2 || $urandom % 5000 == 0);
      if (lfree) begin lreq = $urandom % 3 != 0; ltag = 4'($urandom); end
      if (sfree) begin sreq = $urandom % 3 != 0; stag = 4'($urandom); end
      lval = {$urandom, $urandom};
      lg = $urandom % 2; sg = $urandom % 2; lr = $urandom % 4 == 0; sr = $urandom % 4 == 0;
      lrr = $urandom % 4 != 0; srr = $urandom % 4 != 0;
      #1;
      if (!rst_ni) begin
        if (lgnt || sgnt) errors++;
        lq.delete(); sq.delete(); lheld = 0; sheld = 0; lfree = 1; sfree = 1;
      end else begin
        if (lq.size() == 16 || sq.size() == 16) full++;
        if (lgnt != (lg && lq.size() < 16) || sgnt != (sg && sq.size() < 16)) errors++;
        if (lvalid ? (lq.size() == 0 || {ltag_i, ldata} != lq[0] || (lheld && {ltag_i, ldata} != lprev)) : lheld) errors++;
        if (svalid ? (sq.size() == 0 || stag_i != sq[0] || (sheld && stag_i != sprev)) : sheld) errors++;
        lheld = lvalid && !lrr; lprev = {ltag_i, ldata};
        sheld = svalid && !srr; sprev = stag_i;
        if (lvalid && lrr) begin void'(lq.pop_front()); lpop++; end
        if (svalid && srr) begin void'(sq.pop_front()); spop++; end
        if (lreq && lgnt) begin lq.push_back({ltag, lval}); lpush++; end
        if (sreq && sgnt) begin sq.push_back(stag); spush++; end
        lfree = !lreq || lgnt; sfree = !sreq || sgnt;
      end
      #1 clk = 1;
      #1 clk = 0;
    end
    $display("SERVICE %0d %0d %0d %0d %0d %0d", lpush, lpop, spush, spop, full, errors);
    $finish;
  end
endmodule
"""


def test_random_service_replies_in_grant_order(tmp_path):
    """Every reply carries the tag and load value of the oldest granted request and is held until accepted."""
    tw = timing_witness()
    from prepare_frontend import workspace_root
    bin_dir = workspace_root(HERE) / "tools/oss-cad-suite-20261104/oss-cad-suite/bin"
    if not (bin_dir / "verilator").exists():
        pytest.skip("Verilator from the pinned OSS CAD Suite needed")
    (tmp_path / "tb.sv").write_text(SERVICE_TB.replace("@SERVICE@", tw.RANDOM_SERVICE))
    env = dict(os.environ, PATH=f"{bin_dir}:/usr/bin:/bin")
    subprocess.run([str(bin_dir / "verilator"), "--binary", "-Wno-fatal", "-Wno-lint", "-Wno-style", "--top-module",
                    "tb", "-Mdir", str(tmp_path / "obj"), "-o", "simv", str(tmp_path / "tb.sv")],
                   env=env, check=True, capture_output=True)
    out = subprocess.run([str(tmp_path / "obj/simv"), "+verilator+seed+7"], env=env, check=True,
                         capture_output=True, text=True).stdout
    lpush, lpop, spush, spop, full, errors = map(int, next(
        line for line in out.splitlines() if line.startswith("SERVICE ")).split()[1:])
    assert errors == 0
    assert min(lpush, lpop, spush, spop) > 10000 and full > 1000


# Timing-envelope witness platform ---------------------------------------------

def test_enveloped_platform_gate_per_envelope():
    tw = timing_witness()
    formal = ("module AdmissionScreen(input wire clk_i, rst_ni,\n  input wire [2:0] invalid_code_nonzero, "
              + tw.FAULT_DATA_PORT + "  output wire obs_load);\n  reg [0:0] gap_left;\n"
              + tw.FIXED_GATE + tw.FIXED_SERVICE + "endmodule\n")
    gates = {"legal": "  wire gate_open = 1'b1;\n",
             "refuse1": "  wire gate_open = fetch_gate || refusal_run >= 8'd1;\n",
             "wide": "  wire gate_open = fetch_gate;\n"}
    for envelope, gate in gates.items():
        text = tw.enveloped_platform(formal, envelope)
        assert gate in text and tw.ENVELOPE_SERVICE in text and tw.FAULT_DATA_PORT + tw.ENVELOPE_INPUTS in text
        assert tw.FIXED_GATE not in text and tw.FIXED_SERVICE not in text
        assert all(g not in text for e, g in gates.items() if e != envelope)
    with pytest.raises(ValueError):
        tw.enveloped_platform(formal, "unbounded")
    with pytest.raises(ValueError):
        tw.enveloped_platform(formal.replace(tw.FIXED_SERVICE, ""), "legal")


def test_state_vector_is_msb_first_and_checks_width():
    tw = timing_witness()
    records = [{"cell": "s", "bit": 1}, {"cell": "x", "bit": 0}, {"cell": "s", "bit": 0}, {"cell": "s", "bit": 2}]
    assert tw.state_vector(records, "s", 3) == "{o_ffq[3], o_ffq[0], o_ffq[2]}"
    with pytest.raises(ValueError):
        tw.state_vector(records, "s", 4)
    with pytest.raises(ValueError):
        tw.state_vector(records, "y", 1)


def test_envelope_testbench_uses_the_delay_bound():
    tw = timing_witness()
    records = [{"cell": c, "bit": b} for c, w in
               [(tw.BRANCH_CU, 3), (tw.COMMIT_CU, 5)]
               + [(tw.LOAD_SLOT.format(i), 4) for i in range(tw.LOAD_SLOTS)]
               + [(tw.STORE_SLOT.format(i), 4) for i in range(tw.STORE_SLOTS)] for b in range(w)]
    stores = [(0x2000, 1, 0xff), (0x20000100, 0, 0x01)]
    tb = tw.envelope_testbench(records, "legal", stores, 12)
    start = tb.index("Platform_orig orig(")
    assert all(f".{n}({n})" in tb[start:tb.index(");", start)] for n in tw.ENVELOPE_INPUT_NAMES)
    assert "1 + $urandom % 12);" in tb and "if (lat < 1 || lat > 12) begin" in tb
    assert "longint unsigned load_lat_hist [0:12];" in tb and "for (int i = 0; i <= 12; i++)" in tb
    assert "localparam int NSTORES = 2;" in tb and "1: return {8'h01, 64'h0000000020000100};" in tb
    for bad in (0, 256):
        with pytest.raises(ValueError):
            tw.envelope_testbench(records, "legal", stores, bad)
    assert tw.replaced_timing("legal", 12)["max_reply_delay"] == 12
    assert "expected to fail" in tw.replaced_timing("refuse1", 3)["fetch_gate"]
    assert tw.MAX_REFUSALS == {"legal": 0, "refuse1": 1}


ENVELOPE_SERVICE_TB = r"""
module svc(input wire clk_i, rst_ni, data_load_req_o, data_load_rready_o, data_store_req_o, data_store_rready_o,
  input wire [3:0] data_load_tag_o, data_store_tag_o, input wire [63:0] load_value,
  input wire load_gnt, store_gnt, input wire [7:0] load_lat, store_lat,
  output wire data_load_gnt_i, data_load_rvalid_i, data_store_gnt_i, data_store_rvalid_i,
  output wire [3:0] data_load_tag_i, data_store_tag_i, output wire [63:0] data_load_rdata_i);
@SERVICE@
endmodule

module tb;
  logic clk = 0, rst_ni = 0, lreq = 0, sreq = 0, lrr = 1, srr = 1, lg = 0, sg = 0;
  logic [7:0] llat = 1, slat = 1;
  logic [3:0] ltag = 0, stag = 0;
  logic [63:0] lval = 0;
  wire lgnt, lvalid, sgnt, svalid;
  wire [3:0] ltag_i, stag_i;
  wire [63:0] ldata;
  svc dut(.clk_i(clk), .rst_ni(rst_ni), .data_load_req_o(lreq), .data_load_rready_o(lrr), .data_store_req_o(sreq),
          .data_store_rready_o(srr), .data_load_tag_o(ltag), .data_store_tag_o(stag), .load_value(lval),
          .load_gnt(lg), .store_gnt(sg), .load_lat(llat), .store_lat(slat), .data_load_gnt_i(lgnt),
          .data_load_rvalid_i(lvalid), .data_store_gnt_i(sgnt), .data_store_rvalid_i(svalid),
          .data_load_tag_i(ltag_i), .data_store_tag_i(stag_i), .data_load_rdata_i(ldata));
  // Reference model: replies leave in grant order, each no earlier than its requested delay after its grant.
  logic [67:0] lq [$];
  logic [3:0] sq [$];
  longint ldue [$];
  longint sdue [$];
  longint now = 0;
  logic lfree = 1, sfree = 1;
  longint unsigned lpush = 0, lpop = 0, spush = 0, spop = 0, full = 0, exact = 0, errors = 0;
  initial begin
    for (int cyc = 0; cyc < 200000; cyc++) begin
      rst_ni = !(cyc < 2 || $urandom % 5000 == 0);
      if (lfree) begin lreq = $urandom % 3 != 0; ltag = 4'($urandom); end
      if (sfree) begin sreq = $urandom % 3 != 0; stag = 4'($urandom); end
      lval = {$urandom, $urandom};
      lg = $urandom % 2; sg = $urandom % 2; llat = 8'(1 + $urandom % 9); slat = 8'(1 + $urandom % 9);
      lrr = $urandom % 4 != 0; srr = $urandom % 4 != 0;
      #1;
      if (!rst_ni) begin
        if (lgnt || sgnt) errors++;
        lq.delete(); sq.delete(); ldue.delete(); sdue.delete(); lfree = 1; sfree = 1;
      end else begin
        if (lq.size() == 8 || sq.size() == 8) full++;
        if (lgnt != (lg && lq.size() < 8) || sgnt != (sg && sq.size() < 8)) errors++;
        if (lvalid != (lq.size() != 0 && now >= ldue[0])) errors++;
        if (svalid != (sq.size() != 0 && now >= sdue[0])) errors++;
        if (lvalid && {ltag_i, ldata} != lq[0]) errors++;
        if (svalid && stag_i != sq[0]) errors++;
        if (lvalid && now == ldue[0]) exact++;
        if (lvalid && lrr) begin void'(lq.pop_front()); void'(ldue.pop_front()); lpop++; end
        if (svalid && srr) begin void'(sq.pop_front()); void'(sdue.pop_front()); spop++; end
        if (lreq && lgnt) begin lq.push_back({ltag, lval}); ldue.push_back(now + llat); lpush++; end
        if (sreq && sgnt) begin sq.push_back(stag); sdue.push_back(now + slat); spush++; end
        lfree = !lreq || lgnt; sfree = !sreq || sgnt;
      end
      now = rst_ni ? now + 1 : 0;
      #1 clk = 1;
      #1 clk = 0;
    end
    $display("SERVICE %0d %0d %0d %0d %0d %0d %0d", lpush, lpop, spush, spop, full, exact, errors);
    $finish;
  end
endmodule
"""


def test_envelope_service_delivers_in_order_after_requested_delay(tmp_path):
    """Each reply carries the oldest granted request's tag and value, exactly when its delay has elapsed
    and every older reply has left; grants stop at eight outstanding requests per channel."""
    tw = timing_witness()
    from prepare_frontend import workspace_root
    bin_dir = workspace_root(HERE) / "tools/oss-cad-suite-20261104/oss-cad-suite/bin"
    if not (bin_dir / "verilator").exists():
        pytest.skip("Verilator from the pinned OSS CAD Suite needed")
    (tmp_path / "tb.sv").write_text(ENVELOPE_SERVICE_TB.replace("@SERVICE@", tw.ENVELOPE_SERVICE))
    env = dict(os.environ, PATH=f"{bin_dir}:/usr/bin:/bin")
    subprocess.run([str(bin_dir / "verilator"), "--binary", "-Wno-fatal", "-Wno-lint", "-Wno-style", "--top-module",
                    "tb", "-Mdir", str(tmp_path / "obj"), "-o", "simv", str(tmp_path / "tb.sv")],
                   env=env, check=True, capture_output=True)
    out = subprocess.run([str(tmp_path / "obj/simv"), "+verilator+seed+7"], env=env, check=True,
                         capture_output=True, text=True).stdout
    lpush, lpop, spush, spop, full, exact, errors = map(int, next(
        line for line in out.splitlines() if line.startswith("SERVICE ")).split()[1:])
    assert errors == 0
    assert min(lpush, lpop, spush, spop) > 10000 and full > 100 and exact > 1000


def export_closed():
    sys.path.insert(0, str(HERE.parent))
    sys.path.insert(0, str(HERE.parent / "application_screen"))
    sys.path.insert(0, str(HERE))
    import export_closed as ec
    return ec


FIXED_SERVICE_TB = r"""
module svc(input wire clk_i, rst_ni, data_load_req_o, data_store_req_o,
  input wire [3:0] data_load_tag_o, data_store_tag_o, input wire [63:0] load_value,
  output wire data_load_gnt_i, data_load_rvalid_i, data_store_gnt_i, data_store_rvalid_i,
  output wire [3:0] data_load_tag_i, data_store_tag_i, output wire [63:0] data_load_rdata_i);
@SERVICE@
endmodule

module tb;
  localparam int N = 100000, LAT = @LAT@;
  logic clk = 0, rst_ni = 0, lreq = 0, sreq = 0;
  logic [3:0] ltag = 0, stag = 0;
  logic [63:0] lval = 0;
  wire lgnt, lvalid, sgnt, svalid;
  wire [3:0] ltag_i, stag_i;
  wire [63:0] ldata;
  svc dut(.clk_i(clk), .rst_ni(rst_ni), .data_load_req_o(lreq), .data_store_req_o(sreq), .data_load_tag_o(ltag),
          .data_store_tag_o(stag), .load_value(lval), .data_load_gnt_i(lgnt), .data_load_rvalid_i(lvalid),
          .data_store_gnt_i(sgnt), .data_store_rvalid_i(svalid), .data_load_tag_i(ltag_i),
          .data_store_tag_i(stag_i), .data_load_rdata_i(ldata));
  // Reference: what is presented in cycle t appears at the reply outputs in cycle t + LAT, unless reset is
  // asserted in one of the cycles t .. t + LAT - 1; then the outputs are zero. Every request is granted.
  bit rs [N], rl [N], rq [N];
  logic [3:0] tl [N], ts [N];
  logic [63:0] vl [N];
  longint unsigned replies = 0, errors = 0;
  bit ok;
  initial begin
    for (int t = 0; t < N; t++) begin
      rst_ni = !(t < 2 || $urandom % 500 == 0);
      lreq = $urandom % 2; sreq = $urandom % 2; ltag = 4'($urandom); stag = 4'($urandom); lval = {$urandom, $urandom};
      rs[t] = rst_ni; rl[t] = lreq; rq[t] = sreq; tl[t] = ltag; ts[t] = stag; vl[t] = lval;
      #1;
      begin
        ok = t >= LAT;
        if (ok) for (int k = t - LAT; k < t; k++) if (!rs[k]) ok = 0;
        if (lgnt != rst_ni || sgnt != rst_ni) errors++;
        if (lvalid != (ok && rl[t - LAT]) || svalid != (ok && rq[t - LAT])) errors++;
        if (ltag_i != (ok ? tl[t - LAT] : 4'd0) || stag_i != (ok ? ts[t - LAT] : 4'd0)) errors++;
        if (ldata != (ok ? vl[t - LAT] : 64'd0)) errors++;
        if (lvalid && ok) replies++;
      end
      #1 clk = 1;
      #1 clk = 0;
    end
    $display("FIXED %0d %0d", replies, errors);
    $finish;
  end
endmodule
"""


def test_native_data_service_is_the_harness_text():
    ec, tw = export_closed(), timing_witness()
    assert ec.data_service(ec.NATIVE_DATA_LATENCY) == tw.FIXED_SERVICE
    assert "two-cycle replies" in ec.data_service(2) and "lv <= data_load_req_o;" in ec.data_service(1)
    for bad in (0, 9):
        with pytest.raises(ValueError, match="latency"):
            ec.data_service(bad)


@pytest.mark.parametrize("latency", [1, 2, 3])
def test_fixed_data_service_replies_after_exactly_its_latency(tmp_path, latency):
    """Every request is granted and answered exactly `latency` cycles later with the tag and value presented
    with it; a reset inside that window clears the reply."""
    ec = export_closed()
    from prepare_frontend import workspace_root
    bin_dir = workspace_root(HERE) / "tools/oss-cad-suite-20261104/oss-cad-suite/bin"
    if not (bin_dir / "verilator").exists():
        pytest.skip("Verilator from the pinned OSS CAD Suite needed")
    (tmp_path / "tb.sv").write_text(FIXED_SERVICE_TB.replace("@SERVICE@", ec.data_service(latency))
                                    .replace("@LAT@", str(latency)))
    env = dict(os.environ, PATH=f"{bin_dir}:/usr/bin:/bin")
    subprocess.run([str(bin_dir / "verilator"), "--binary", "-Wno-fatal", "-Wno-lint", "-Wno-style", "--top-module",
                    "tb", "-Mdir", str(tmp_path / "obj"), "-o", "simv", str(tmp_path / "tb.sv")],
                   env=env, check=True, capture_output=True)
    out = subprocess.run([str(tmp_path / "obj/simv"), "+verilator+seed+7"], env=env, check=True,
                         capture_output=True, text=True).stdout
    replies, errors = map(int, next(line for line in out.splitlines() if line.startswith("FIXED ")).split()[1:])
    assert errors == 0 and replies > 40000


# Evidence collector -------------------------------------------------------------

def collector():
    sys.path.insert(0, str(HERE))
    import collect_evidence as ce
    return ce


def test_collector_classifies_negative_control_failures():
    ce = collector()
    assert ce.failure_kind("seed 1: lost_redirects detected 20 time(s), first at cycle 5493") == \
        "lost_redirects (monitor)"
    assert ce.failure_kind("seed 8: 2 of 65 stores in the 49998 cycles after the last reset") == \
        "store count after the last reset differs from the reference"
    assert ce.failure_kind("seed 1004: stores differ from the recorded RTL simulation") == \
        "stores differ from the recorded RTL simulation"


def test_collector_constant_sets_and_breakdown(tmp_path):
    ce = collector()
    rs = "$driver$u_backend.u_exec_stage.u_alu_unit.u_arith_rs."
    entries = [{"cell": rs + "data[5].rs2_value", "bit": 3, "net": 9, "value": 1},
               {"cell": rs + "curr_state[2]", "bit": 0, "net": 7, "value": 0},
               {"cell": "$driver$u_backend.u_csrs.mcycle", "bit": 0, "net": 4, "value": 0}]
    (tmp_path / "constants.json").write_text(json.dumps({"constants": entries}))
    (tmp_path / "applied.json").write_text(json.dumps(entries))
    found = ce.constant_set(tmp_path / "constants.json")
    assert found == ce.constant_set(tmp_path / "applied.json", None)
    assert found[(rs + "data[5].rs2_value", 3)] == (9, 1)
    split = ce.breakdown(set(found))
    assert split["bits"] == 3 and split["by_alu_rs_row"] == {"2": 1, "5": 1, "other": 1}
    assert split["by_field"] == {"u_backend.u_exec_stage.u_alu_unit.u_arith_rs.data[].rs2_value": 1,
                                 "u_backend.u_exec_stage.u_alu_unit.u_arith_rs.curr_state[]": 1,
                                 "u_backend.u_csrs.mcycle": 1}
