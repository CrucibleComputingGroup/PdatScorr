#!/usr/bin/env bash
# PwF with microarchitecture-aware error injection on the corrected core, 16 subsets,
# and the negative controls of its proof.
#
#   run_injection.sh [OUT] [RUNS]
#     OUT   default $WS/experiments/rissp_table_regen/final
#     RUNS  finished sweep-only runs under OUT to start from (default pwf_fixed_inreset);
#           results go to OUT/RUNS_inject and OUT/RUNS_inject_control
#
# All runs start in parallel.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
OUT=${1:-$WS/experiments/rissp_table_regen/final}
RUNS=${2:-pwf_fixed_inreset}
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
CFGS="0000 0001 0010 0011 0100 0101 0110 0111 1000 1001 1010 1011 1100 1101 1110 1111"
mkdir -p "$OUT/logs"
for cfg in $CFGS; do
  [ -f "$OUT/${RUNS}_inject/$cfg/injection_report.json" ] || \
    python3 "$HERE/error_injection/inject.py" "$OUT/$RUNS/$cfg" "$OUT/${RUNS}_inject/$cfg" \
      > "$OUT/logs/${RUNS}_inject_$cfg.log" 2>&1 &
  [ -f "$OUT/${RUNS}_inject_control/$cfg/control_report.json" ] || \
    python3 "$HERE/error_injection/inject.py" --control "$OUT/$RUNS/$cfg" "$OUT/${RUNS}_inject_control/$cfg" \
      > "$OUT/logs/${RUNS}_control_$cfg.log" 2>&1 &
done
wait
cat "$OUT"/logs/${RUNS}_inject_*.log
cat "$OUT"/logs/${RUNS}_control_*.log
