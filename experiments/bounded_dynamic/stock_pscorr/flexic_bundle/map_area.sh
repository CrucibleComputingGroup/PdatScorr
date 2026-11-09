#!/usr/bin/env bash
# Map one optimized AIG to a standard-cell library and report its cell area.
#
#   map_area.sh LIBERTY AIG TOP CLOCK OUT_PREFIX
#
# The commands are exactly those that produced the paper's SKY130 areas (Yosys 0.33):
# flip-flops via dfflibmap, logic via ABC's `strash; dretime; map`, area from
# `stat -liberty`. That ABC script is what `abc -fast` runs for Liberty mapping in
# Yosys 0.33; newer Yosys no longer accepts `-fast`, so it is given explicitly.
# With Yosys 0.33 both forms give identical netlists.
# Writes OUT_PREFIX.ys, OUT_PREFIX.log, OUT_PREFIX.gates.v and prints the area.
# Set YOSYS=/path/to/yosys to choose the binary (default: yosys on PATH).
set -euo pipefail
if [ $# -ne 5 ]; then
  echo "usage: $0 LIBERTY AIG TOP CLOCK OUT_PREFIX" >&2
  exit 2
fi
LIB=$(realpath "$1"); AIG=$(realpath "$2"); TOP=$3; CLK=$4; OUT=$5
YOSYS=${YOSYS:-yosys}
mkdir -p "$(dirname "$OUT")"
cat > "$OUT.ys" <<EOF
read_aiger -clk_name $CLK $AIG
flatten
opt
memory
opt_clean
fsm
opt
techmap
opt
dfflibmap -liberty $LIB
abc -liberty $LIB -script "+strash;dretime;map"
opt_clean
rename -top $TOP
write_verilog -noattr -noexpr -nohex $OUT.gates.v
stat
stat -liberty $LIB
EOF
"$YOSYS" -q -l "$OUT.log" -s "$OUT.ys" > /dev/null
AREA=$(grep -E "Chip area for (top )?module" "$OUT.log" | tail -1 | sed -E 's/.*: *([0-9.eE+-]+).*/\1/')
if [ -z "$AREA" ]; then
  echo "no area reported; see $OUT.log" >&2
  exit 1
fi
echo "$AREA"
