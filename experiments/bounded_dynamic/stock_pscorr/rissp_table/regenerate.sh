#!/usr/bin/env bash
# Regenerate the single-cycle RISSP comparison (paper Table 1) and the checks behind
# README.md, with the paper's experiment checkout.
#
#   regenerate.sh [OUT]      default OUT: $WS/experiments/rissp_table_regen/final
#
# Three versions of the core are assembled under OUT/cores:
#   paper   the RTL revision of the original runs (PdatCoreSim commit 1682660)
#   minfix  paper, with only the divider's case items rewritten (cores/minfix/mdu.sv)
#   fixed   complete M extension and an address adder that is always present
#           (cores/fixed/mdu.sv, cores/fixed/alu.sv)
# The PwF flow (the checkout's synth_core.sh, constraint + sequential sweep) runs on all
# three for the 16 subsets; the module-level baseline (run_baseline.sh) runs on fixed.
# All 64 runs start in parallel; allow about 5 minutes.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
OUT=${1:-$WS/experiments/rissp_table_regen/final}
# Experiment checkout: PdatScorr flow, PdatRiscvDsl, Synlig.
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
CORESIM=$PSCORR_TREE/PdatCoreSim
SAVED=$CORESIM/cores/RiscvSingleCycle/synthesis_results   # the runs behind the RISSP column
CFGS="0000 0001 0010 0011 0100 0101 0110 0111 1000 1001 1010 1011 1100 1101 1110 1111"
mkdir -p "$OUT/logs"

# 1. Cores and flow configurations.
for core in paper minfix fixed; do
  mkdir -p "$OUT/cores/$core/target" "$OUT/configs/$core"
  for f in alu branch_comp control datapath immgen mdu regfile riscv_core; do
    git -C "$CORESIM" show "1682660:cores/RiscvSingleCycle/target/$f.sv" > "$OUT/cores/$core/target/$f.sv"
  done
  [ "$core" = paper ] || cp "$HERE/cores/$core"/*.sv "$OUT/cores/$core/target/"
  sed "s#core_root: \".*\"#core_root: \"$OUT/cores/$core\"#" "$PSCORR_SYNTHESIS_DIR/configs/riscvsinglecycle.yaml" \
    > "$OUT/configs/$core/riscvsinglecycle.yaml"
done

# 2. PwF flow on the three cores and the module-level baseline on the corrected core.
cd "$PSCORR_SYNTHESIS_DIR"
for core in paper minfix fixed; do
  for cfg in $CFGS; do
    [ -f "$OUT/pwf_$core/$cfg/riscvsinglecycle_optimized_gates.log" ] && continue
    ./synth_core.sh --core riscvsinglecycle --config "$OUT/configs/$core/riscvsinglecycle.yaml" --gates \
      "experiments/modular_equiv/$cfg.dsl" "$OUT/pwf_$core" > "$OUT/logs/pwf_${core}_$cfg.log" 2>&1 &
  done
done
for cfg in $CFGS; do
  [ -f "$OUT/base_fixed/$cfg/baseline_gates.log" ] && continue
  "$HERE/run_baseline.sh" "$OUT/cores/fixed" "$cfg" "$OUT/base_fixed" > "$OUT/logs/base_fixed_$cfg.log" 2>&1 &
done
wait

# 3. Input/output maps of the AIGs, for the instruction-level test. write_aiger orders
#    the ports as the front end read them, which differs between the two flows.
#    (a) PwF flow: rerun one generated script with -map and check the AIG is unchanged.
mkdir -p "$OUT/maps/pwf" "$OUT/maps/saved"
sed -e "s#^write_aiger -zinit .*#write_aiger -zinit -map $OUT/maps/pwf.map $OUT/maps/pwf/check.aig#" \
  "$OUT/pwf_paper/0000/riscvsinglecycle_optimized_synth.ys" > "$OUT/maps/pwf/synth_map.ys"
(cd "$OUT/maps/pwf" && SLPP_ALL="$OUT/maps/pwf/slpp_all" synlig -s synth_map.ys > synlig.log 2>&1)
cmp "$OUT/maps/pwf/check.aig" "$OUT/pwf_paper/0000/riscvsinglecycle_optimized_yosys.aig"
#    (b) Saved RISSP-column runs: rerun the saved script of the full configuration.
cp "$SAVED"/mul1_div1_add1_shift1/target_sv/*.sv "$OUT/maps/saved/"
sed -e "s#^write_aiger -zinit .*#write_aiger -zinit -map $OUT/maps/saved.map $OUT/maps/saved/check.aig#" \
  "$SAVED/mul1_div1_add1_shift1/synth_script.ys" > "$OUT/maps/saved/synth_map.ys"
(cd "$OUT/maps/saved" && SLPP_ALL="$OUT/maps/saved/slpp_all" synlig -s synth_map.ys > synlig.log 2>&1)
cmp "$OUT/maps/saved/check.aig" "$SAVED/mul1_div1_add1_shift1/yosys.aig"
rm -rf "$OUT/maps/pwf/slpp_all" "$OUT/maps/saved/slpp_all"

# 4. Tables: results/*.csv next to this script.
python3 "$HERE/tabulate.py" "$OUT" "$SAVED" "$HERE/results"
