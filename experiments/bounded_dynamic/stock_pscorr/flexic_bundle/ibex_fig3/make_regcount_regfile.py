#!/usr/bin/env python3
"""Write an Ibex flip-flop register file that keeps only registers x1..x(REGS-1).

    make_regcount_regfile.py SOURCE_RTL REGS OUTPUT

The registers that the constraints forbid get no storage and read as zero. This is the
form of the ODC register-file optimization that the experiment checkout used when the
register-count results were first produced (2025-11-07). A copy of that file for four
registers survives in the checkout's Surelog cache
(PdatScorr/slpp_all/lib/work/output/04regs/odc_optimized_rtl/); this script reproduces
it byte for byte. The checkout's committed scripts/apply_odc_optimizations.py (from
2025-11-08) writes a different form, which shrinks the register array and clamps the
read address.
"""
import sys
from pathlib import Path

OLD = """    logic [DataWidth-1:0] rf_reg_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q <= WordZeroVal;
      end else if (we_a_dec[i]) begin
        rf_reg_q <= wdata_a_i;
      end
    end

    assign rf_reg[i] = rf_reg_q;
  end
"""
BLANK = "  \n"  # the original has two spaces on its blank lines
NEW = ("""    // ODC OPTIMIZATION: Only generate registers 1..{last}
    if (i <= {last}) begin
      logic [DataWidth-1:0] rf_reg_q;
""" + BLANK + """      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rf_reg_q <= WordZeroVal;
        end else if (we_a_dec[i]) begin
          rf_reg_q <= wdata_a_i;
        end
      end
""" + BLANK + """      assign rf_reg[i] = rf_reg_q;
    end else begin
      // Unused registers - tie to constant 0
      assign rf_reg[i] = '0;
    end
  end  // g_rf_flops
""")


def main() -> int:
    source, regs, output = Path(sys.argv[1]), int(sys.argv[2]), Path(sys.argv[3])
    text = source.read_text()
    if not 1 < regs < 32:
        raise SystemExit("REGS must be between 2 and 31")
    if text.count(OLD) != 1:
        raise SystemExit("register storage loop not found exactly once")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text.replace(OLD, NEW.format(last=regs - 1)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
