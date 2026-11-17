#!/usr/bin/env bash
# Module-level (RISSP-style) baseline: the single-cycle core with unit switches and no
# instruction-set constraint.
#
#   run_baseline.sh CORE CFG OUTDIR
#     CORE    directory holding target/*.sv (the RTL of the core)
#     CFG     four digits {mul}{div}{add}{shift}, 1 = unit present
#     OUTDIR  results go to OUTDIR/CFG
#
# Front end, Yosys script, ABC script and gate mapping are those of the PwF flow
# (synth_core.sh). The only differences are that units are removed by RTL parameters and
# that no constraint is given.
set -euo pipefail
CORE=$1; CFG=$2; OUTDIR=$3
WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
RUN=$OUTDIR/$CFG
mkdir -p "$RUN/core/target"
cp "$CORE"/target/*.sv "$RUN/core/target/"
M=${CFG:0:1}; D=${CFG:1:1}; A=${CFG:2:1}; S=${CFG:3:1}
# Unit switches: change the defaults of the top-level parameters; they are passed down.
sed -i -E "s/(parameter bit ENABLE_MUL +)= 1/\1= $M/; s/(parameter bit ENABLE_DIV +)= 1/\1= $D/; s/(parameter bit ENABLE_ADDER +)= 1/\1= $A/; s/(parameter bit ENABLE_SHIFTER +)= 1/\1= $S/" "$RUN/core/target/riscv_core.sv"
grep -E "parameter bit ENABLE_(MUL|DIV|ADDER|SHIFTER)" "$RUN/core/target/riscv_core.sv" > "$RUN/parameters.txt"
sed "s#core_root: \".*\"#core_root: \"$RUN/core\"#" "$PSCORR_SYNTHESIS_DIR/configs/riscvsinglecycle.yaml" > "$RUN/riscvsinglecycle.yaml"
BASE=$RUN/baseline
cd "$PSCORR_SYNTHESIS_DIR"
python3 scripts/make_synthesis_script.py --config "$RUN/riscvsinglecycle.yaml" -o "${BASE}_synth.ys" -a "$BASE" > "$RUN/make_script.log" 2>&1
# Also write the input/output map of the AIG, which the instruction-level test needs. The
# name must not end in .map: the front end reads *.map files in its working directory.
sed -i -E "s#^write_aiger -zinit (.*)#write_aiger -zinit -map ${BASE}.portmap \1#" "${BASE}_synth.ys"
export SLPP_ALL="$RUN/slpp_all"
(cd "$RUN" && synlig -s "$(basename "${BASE}_synth.ys")") > "${BASE}_yosys.log" 2>&1
# The ABC command of synth_core.sh, without the constraint-removal commands.
abc -c "read_aiger ${BASE}_yosys.aig; strash; cycle 100; scorr -c -m -F 1 -C 30000 -S 20 -v; rewrite -l; balance -l; print_stats; write_aiger ${BASE}_post_abc.aig" > "${BASE}_abc.log" 2>&1
./scripts/synth_to_gates.sh "$BASE" "" clk RiscvSingleCycle_riscv_core > "${BASE}_gates_run.log" 2>&1
rm -rf "$RUN/slpp_all"
echo "$CFG $(grep 'i/o' "${BASE}_abc.log" | tail -1 | sed 's/.*and = *\([0-9]*\).*/\1/') $(grep 'Chip area for module' "${BASE}_gates.log" | tail -1 | awk '{print $NF}')"
