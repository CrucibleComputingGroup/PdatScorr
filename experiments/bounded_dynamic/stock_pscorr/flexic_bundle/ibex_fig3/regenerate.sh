#!/usr/bin/env bash
# Regenerate the 13 Ibex netlists of paper Fig. 3 with the paper's experiment checkout.
#
#   regenerate.sh [OUT]      default OUT: $WS/experiments/ibex_fig3_regen/final
#
# Runs the checkout's own synth_core.sh for each constraint file in dsl/, then compares
# every netlist with the AND count, SKY130 area and FMax recorded for the paper
# (tabulate.py). All 13 runs are started in parallel; allow about 15 minutes.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
OUT=${1:-$WS/experiments/ibex_fig3_regen/final}
# Experiment checkout: PdatScorr flow, PdatRiscvDsl, Synlig, Ibex RTL (sets IBEX_ROOT).
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
mkdir -p "$OUT/logs"
cd "$PSCORR_SYNTHESIS_DIR"

# (b) ISA subsets: constraints only.
for dsl in "$HERE"/dsl/isa_subsets/*.dsl; do
  ./synth_core.sh --core ibex --gates "$dsl" "$OUT/isa_subsets" \
    > "$OUT/logs/isa_$(basename "$dsl" .dsl).log" 2>&1 &
done

# (a) Register count: constraints, then the flow's ODC analysis, which removes the
# storage of the forbidden registers and re-synthesizes.
for dsl in "$HERE"/dsl/reg_count/*.dsl; do
  ./synth_core.sh --core ibex --gates --odc-analysis "$dsl" "$OUT/reg_count_odc" \
    > "$OUT/logs/reg_$(basename "$dsl" .dsl).log" 2>&1 &
done

# (c) Data width: RV32I with registers x1-x31 narrowed to 8, 16 or 24 bits. The flow
# picks up a replacement register file from <run>/odc_optimized_rtl/.
for w in 08 16 24 32; do
  run=$OUT/data_width/writeconcat
  if [ "$w" != 32 ]; then
    python3 "$HERE/make_narrow_regfile.py" "$IBEX_ROOT/rtl/ibex_register_file_ff.sv" "$((10#$w))" writeconcat \
      "$run/width$w/odc_optimized_rtl/ibex_register_file_ff_optimized.sv"
  fi
  ./synth_core.sh --core ibex --gates "$HERE/dsl/data_width/width$w.dsl" "$run" \
    > "$OUT/logs/width_$w.log" 2>&1 &
done

wait
python3 "$HERE/tabulate.py" "$OUT"
