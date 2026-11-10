#!/usr/bin/env bash
# Re-synthesize Ibex with a given optimized register file, as the flow's ODC step does.
#
#   odc_resynth.sh DSL REGISTER_FILE RUN_DIR
#
# Repeats the "Re-synthesizing with ODC optimizations" part of the experiment checkout's
# synth_core.sh (same synthesis call, same ABC command, same gate mapping and timing) for
# a register file supplied by the caller instead of the one the checkout's
# scripts/apply_odc_optimizations.py writes. Uses the flow's folder layout:
#   RUN_DIR/odc_optimized_rtl/ibex_register_file_ff_optimized.sv        the register file
#   RUN_DIR/odc_optimized_synthesis/ibex_register_file_ff_optimized_*   the results
set -euo pipefail
WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
dsl=$(realpath "$1"); regfile=$(realpath "$2"); mkdir -p "$3"; run=$(realpath "$3")
base=ibex_register_file_ff_optimized
depth=2  # k-induction depth of the 2-stage Ibex (configs/ibex.yaml)
rtl=$run/odc_optimized_rtl
out=$run/odc_optimized_synthesis
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
cd "$PSCORR_SYNTHESIS_DIR"
mkdir -p "$rtl" "$out"
cp "$regfile" "$rtl/$base.sv"
cp "$regfile" "$out/$base.sv"

# The flow's synthesis call. It takes the register file from RUN_DIR/odc_optimized_rtl/.
python3 - "$out/$base.sv" "$dsl" "$out" "$depth" <<'EOF'
import sys
from pathlib import Path
sys.path.insert(0, 'odc')
from synthesis import synthesize_error_injected_circuit
result = synthesize_error_injected_circuit(
    error_injected_rtl=Path(sys.argv[1]), dsl_file=Path(sys.argv[2]), output_dir=Path(sys.argv[3]),
    config_file=Path('configs/ibex.yaml'), k_depth=int(sys.argv[4]))
sys.exit(0 if result else 1)
EOF
grep -q "$rtl/$base.sv" "$out/${base}_synth.ys" || { echo "the register file was not used" >&2; exit 1; }

yosys_aig=$out/${base}_yosys.aig
stats=$(abc -c "read_aiger $yosys_aig; print_stats" 2>&1 | grep "i/o")
removal=""
if echo "$stats" | grep -q "(c="; then
  total=$(echo "$stats" | grep -oP 'i/o\s*=\s*\d+/\s*\K\d+')
  constraints=$(echo "$stats" | grep -oP '\(c=\K\d+')
  removal="constr -r;"
  for ((i = total - 1; i >= total - constraints; i--)); do removal="$removal removepo -N $i;"; done
fi
abc -c "
    read_aiger $yosys_aig;
    strash;
    cycle 100;
    scorr -c -m -F $depth -C 30000 -S 20 -v;
    $removal
    rewrite -l;
    fraig;
    balance -l;
    print_stats;
    write_aiger $out/${base}_post_abc.aig;
" > "$out/abc.log" 2>&1
./scripts/synth_to_gates.sh "$out/$base" "" clk_i ibex_core_with_rf > "$out/gates_and_timing.log" 2>&1
printf '%s: %s AND gates, %s um2, %s MHz\n' "$run" \
  "$(head -n1 "$out/${base}_post_abc.aig" | cut -d' ' -f6)" "$(cat "$out/${base}_total_area.txt")" \
  "$(python3 -c "import json; print(json.load(open('$out/${base}_timing_metrics.json'))['max_frequency_mhz'])")"
