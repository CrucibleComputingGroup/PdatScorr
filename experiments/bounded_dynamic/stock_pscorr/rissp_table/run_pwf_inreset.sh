#!/usr/bin/env bash
# PwF variant: the generated instruction constraint also holds while reset is asserted.
#
#   run_pwf_inreset.sh SRC_RUN DST_RUN
#
# SRC_RUN is a finished synth_core.sh run (one subset). The injected top-level file and
# the generated Yosys script are copied, the reset exemption "!rst_n ||" is removed from
# the assumption, and the same front end, ABC command and gate mapping are run.
set -euo pipefail
SRC=$1; DST=$2
WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
P=riscvsinglecycle_optimized
mkdir -p "$DST"
grep -q 'assume (!rst_n || ' "$SRC/${P}_id_stage.sv"
sed 's/assume (!rst_n || /assume (/' "$SRC/${P}_id_stage.sv" > "$DST/${P}_id_stage.sv"
sed 's/assume (!rst_n || /assume (/' "$SRC/${P}_assumptions.sv" > "$DST/${P}_assumptions.sv"
sed "s#$SRC/#$DST/#g" "$SRC/${P}_synth.ys" > "$DST/${P}_synth.ys"
export SLPP_ALL="$DST/slpp_all"
(cd "$DST" && synlig -s "${P}_synth.ys") > "$DST/${P}_yosys.log" 2>&1
abc -c "read_aiger $DST/${P}_yosys.aig; strash; cycle 100; scorr -c -m -F 1 -C 30000 -S 20 -v; constr -r; removepo -N 98; rewrite -l; balance -l; print_stats; write_aiger $DST/${P}_post_abc.aig" > "$DST/${P}_abc.log" 2>&1
cd "$PSCORR_SYNTHESIS_DIR"
./scripts/synth_to_gates.sh "$DST/$P" "" clk RiscvSingleCycle_riscv_core > "$DST/${P}_gates_run.log" 2>&1
rm -rf "$DST/slpp_all"
echo "$(basename "$DST") $(grep 'i/o' "$DST/${P}_abc.log" | tail -1 | sed 's/.*and = *\([0-9]*\).*/\1/') $(grep 'Chip area for module' "$DST/${P}_gates.log" | tail -1 | awk '{print $NF}')"
