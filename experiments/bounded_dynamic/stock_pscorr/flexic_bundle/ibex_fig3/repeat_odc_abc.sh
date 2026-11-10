#!/usr/bin/env bash
# Measure the run-to-run variation of the ABC step of an ODC re-synthesis.
#
#   repeat_odc_abc.sh RUN_DIR [SAMPLES] [map]
#
# RUN_DIR is a register-count run of regenerate.sh (for example OUT/reg_count_odc/08regs).
# Each sample repeats the flow's ABC command on the run's unchanged Yosys netlist. With
# "map", each sample is also mapped and timed with the flow's own script. Prints how
# often each AND count (and area) occurs. Samples go to RUN_DIR/odc_repeat/sNNN/.
set -euo pipefail
WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
run=$(realpath "$1"); samples=${2:-32}; map=${3:-}
base=ibex_register_file_ff_optimized
src=$run/odc_optimized_synthesis
out=$run/odc_repeat
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
mkdir -p "$out"
# The flow's ABC command for the ODC re-synthesis (synth_core.sh), with its constraint removal.
removal=$(grep -o 'constr -r;[^"]*removepo -N [0-9]*;' "$src/abc.log" | head -1)
[ -n "$removal" ] || { echo "constraint removal not found in $src/abc.log" >&2; exit 1; }

one() {
  local d; d=$out/s$(printf '%03d' "$1")
  mkdir -p "$d"
  ( cd "$d" && abc -c "read_aiger $src/${base}_yosys.aig; strash; cycle 100; scorr -c -m -F 2 -C 30000 -S 20 -v; $removal rewrite -l; fraig; balance -l; print_stats; write_aiger $d/${base}_post_abc.aig" > abc.log 2>&1 )
  if [ "$map" = map ]; then
    ( cd "$PSCORR_SYNTHESIS_DIR" && ./scripts/synth_to_gates.sh "$d/$base" "" clk_i ibex_core_with_rf > "$d/gates_and_timing.log" 2>&1 ) || true
  fi
}
for i in $(seq 1 "$samples"); do one "$i" & done
wait

echo "distinct netlist files: $(sha256sum "$out"/s*/${base}_post_abc.aig | cut -d' ' -f1 | sort -u | wc -l) in $samples samples"
echo "AND gates (count x value):"
for f in "$out"/s*/${base}_post_abc.aig; do head -n1 "$f" | cut -d' ' -f6; done | sort | uniq -c
if [ "$map" = map ]; then
  echo "SKY130 area (count x value):"
  cat "$out"/s*/${base}_total_area.txt | sort | uniq -c
fi
