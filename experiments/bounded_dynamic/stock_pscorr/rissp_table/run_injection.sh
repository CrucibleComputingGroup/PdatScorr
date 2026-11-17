#!/usr/bin/env bash
# PwF with microarchitecture-aware error injection on the corrected core, 16 subsets,
# and the negative controls of its proof.
#
#   run_injection.sh [OUT]     default OUT: $WS/experiments/rissp_table_regen/final
#
# Needs the pwf_fixed runs of regenerate.sh. All runs start in parallel.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
OUT=${1:-$WS/experiments/rissp_table_regen/final}
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
CFGS="0000 0001 0010 0011 0100 0101 0110 0111 1000 1001 1010 1011 1100 1101 1110 1111"
mkdir -p "$OUT/logs"
for cfg in $CFGS; do
  [ -f "$OUT/pwf_fixed_inject/$cfg/injection_report.json" ] || \
    python3 "$HERE/error_injection/inject.py" "$OUT/pwf_fixed/$cfg" "$OUT/pwf_fixed_inject/$cfg" \
      > "$OUT/logs/inject_$cfg.log" 2>&1 &
  [ -f "$OUT/pwf_fixed_inject_control/$cfg/control_report.json" ] || \
    python3 "$HERE/error_injection/inject.py" --control "$OUT/pwf_fixed/$cfg" "$OUT/pwf_fixed_inject_control/$cfg" \
      > "$OUT/logs/control_$cfg.log" 2>&1 &
done
wait
cat "$OUT"/logs/inject_*.log
cat "$OUT"/logs/control_*.log
