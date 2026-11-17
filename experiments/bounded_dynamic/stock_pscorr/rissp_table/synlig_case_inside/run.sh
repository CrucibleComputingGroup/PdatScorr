#!/usr/bin/env bash
# Elaborate each module with the flow's front end and print the comparisons on op that
# the netlist contains.   run.sh [SCRATCH_DIR]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
T=${1:-$(mktemp -d)}
mkdir -p "$T" && cd "$T"
synlig -V | head -1
for m in pair range two_pairs pair_gap inside_range_expr three_values single plain_case inside_expr; do
  printf 'read_systemverilog %s/%s.sv\nhierarchy -top %s\nproc; opt -full; opt_clean\nwrite_verilog -noattr %s.v\n' "$HERE" "$m" "$m" "$m" > "$m.ys"
  rm -rf slpp_all
  synlig -s "$m.ys" > "$m.log" 2>&1
  printf '%-18s %s\n' "$m" "$(grep -E 'assign' "$m.v" | grep -E 'op' | sed 's/^ *assign //' | tr '\n' ' ')"
done
