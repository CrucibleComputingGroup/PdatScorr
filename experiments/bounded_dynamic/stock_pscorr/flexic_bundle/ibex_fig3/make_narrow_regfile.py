#!/usr/bin/env python3
"""Write an Ibex flip-flop register file whose registers x1-x31 hold only WIDTH bits.

Reconstruction of the data-width study of paper Fig. 3(c). The original modified
register file was not preserved; a result is accepted only when the regenerated netlist
reproduces the recorded AND count and SKY130 area exactly. Several equivalent ways of
writing the same narrowing are provided, because the synthesized netlist depends on the
form of the RTL.

Usage: make_narrow_regfile.py SOURCE_RTL WIDTH STYLE OUTPUT

Zero-extending styles (the register reads back its low WIDTH bits, upper bits 0):
  write        extra assignment clearing the upper bits on every write
  writeconcat  the written value is {0, wdata[WIDTH-1:0]}
  writemask    the written value is wdata & mask
  read         the stored value is read as {0, q[WIDTH-1:0]}
  narrowflop   the flops themselves are WIDTH bits wide
  arraydecl    the register array is declared WIDTH bits wide
  rdatamask    the read ports return {0, reg[WIDTH-1:0]}
Sign-extending styles (a different function, tried for completeness):
  signwrite    the written value is sign-extended from bit WIDTH-1
  signread     the stored value is read sign-extended from bit WIDTH-1
"""
import sys
from pathlib import Path

DECL_ARRAY = "  logic [DataWidth-1:0] rf_reg   [NUM_WORDS];\n"
DECL_FLOP = "    logic [DataWidth-1:0] rf_reg_q;\n\n    always_ff @(posedge clk_i or negedge rst_ni) begin\n"
RESET = "        rf_reg_q <= WordZeroVal;\n"
WRITE = "        rf_reg_q <= wdata_a_i;\n"
READ = "    assign rf_reg[i] = rf_reg_q;\n"
RDATA_A = "    assign rdata_a_o = rf_reg[raddr_a_i];\n"
RDATA_B = "    assign rdata_b_o = rf_reg[raddr_b_i];\n"


def swap(text: str, old: str, new: str) -> str:
    if text.count(old) != 1:
        raise SystemExit(f"expected exactly one occurrence of: {old.strip()}")
    return text.replace(old, new)


def narrow(text: str, w: int, style: str) -> str:
    zeros = f"{{(DataWidth-{w}){{1'b0}}}}"
    note = f"// Narrow data: x1-x31 hold {w} bits"
    if style == "write":
        return swap(text, WRITE, WRITE + f"        {note}; upper bits tied to 0\n"
                                         f"        rf_reg_q[DataWidth-1:{w}] <= '0;\n")
    if style == "writeconcat":
        return swap(text, WRITE, f"        {note}; upper bits tied to 0\n"
                                 f"        rf_reg_q <= {{{zeros}, wdata_a_i[{w - 1}:0]}};\n")
    if style == "writemask":
        return swap(text, WRITE, f"        {note}; upper bits tied to 0\n"
                                 f"        rf_reg_q <= wdata_a_i & 32'h{(1 << w) - 1:08x};\n")
    if style == "signwrite":
        return swap(text, WRITE, f"        {note}; sign-extended\n"
                                 f"        rf_reg_q <= {{{{(DataWidth-{w}){{wdata_a_i[{w - 1}]}}}}, wdata_a_i[{w - 1}:0]}};\n")
    if style == "read":
        return swap(text, READ, f"    {note}; upper bits read as 0\n"
                                f"    assign rf_reg[i] = {{{zeros}, rf_reg_q[{w - 1}:0]}};\n")
    if style == "signread":
        return swap(text, READ, f"    {note}; read sign-extended\n"
                                f"    assign rf_reg[i] = {{{{(DataWidth-{w}){{rf_reg_q[{w - 1}]}}}}, rf_reg_q[{w - 1}:0]}};\n")
    if style == "narrowflop":
        text = swap(text, DECL_FLOP, DECL_FLOP.replace("[DataWidth-1:0]", f"[{w - 1}:0]"))
        text = swap(text, RESET, f"        rf_reg_q <= WordZeroVal[{w - 1}:0];\n")
        text = swap(text, WRITE, f"        rf_reg_q <= wdata_a_i[{w - 1}:0];\n")
        return swap(text, READ, f"    {note}; upper bits read as 0\n"
                                f"    assign rf_reg[i] = {{{zeros}, rf_reg_q}};\n")
    if style == "arraydecl":
        return swap(text, DECL_ARRAY, f"  {note}\n  logic [{w - 1}:0] rf_reg   [NUM_WORDS];\n")
    if style == "rdatamask":
        text = swap(text, RDATA_A, f"    {note}; upper bits read as 0\n"
                                   f"    assign rdata_a_o = {{{zeros}, rf_reg[raddr_a_i][{w - 1}:0]}};\n")
        return swap(text, RDATA_B, f"    assign rdata_b_o = {{{zeros}, rf_reg[raddr_b_i][{w - 1}:0]}};\n")
    raise SystemExit(f"unknown STYLE: {style}")


def main() -> int:
    source, width, style, output = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3], Path(sys.argv[4])
    if not 0 < width < 32:
        raise SystemExit("WIDTH must be between 1 and 31")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(narrow(source.read_text(), width, style))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
