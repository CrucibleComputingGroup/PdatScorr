#!/usr/bin/env bash
# Try one way of writing the data-width narrowing of paper Fig. 3(c).
#
#   explore_width_form.sh FORM WIDTH [OUT]     default OUT: $WS/experiments/ibex_fig3_regen
#
# FORM is a style of make_narrow_regfile.py (a change inside the register file), or
#   param  the wrapper's RegFileDataWidth parameter is set to WIDTH (core and register file)
#   inst   only the register-file instance gets DataWidth = WIDTH
# Output: OUT/data_width/FORM/widthWW/ ; log: OUT/logs/width_FORM_WW.log
# This is how the form used by regenerate.sh (writeconcat) was identified; see README.md.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
WS=${WS:-/home/allenjin/Projects/DAC_pscorr}
form=$1
width=$2
OUT=${3:-$WS/experiments/ibex_fig3_regen}
w=$(printf '%02d' "$width")
run=$OUT/data_width/$form
SNAP=$WS/experiments/PdatProjectForrocket
# shellcheck disable=SC1091
source "$WS/scripts/env.sh" paper
mkdir -p "$run" "$OUT/logs"
case "$form" in
  param|inst)
    # The wrapper is not an injection point of the flow, so use a private copy of the flow scripts.
    flow=$OUT/data_width/flows/${form}_w$w
    rm -rf "$flow"
    mkdir -p "$flow/PdatScorr"
    cp -r "$SNAP/PdatScorr/synth_core.sh" "$SNAP/PdatScorr/scripts" "$SNAP/PdatScorr/configs" \
          "$SNAP/PdatScorr/odc" "$SNAP/PdatScorr/ibex_core_with_rf.sv" "$flow/PdatScorr/"
    ln -s "$SNAP/PdatRiscvDsl" "$flow/PdatRiscvDsl"
    wrapper=$flow/PdatScorr/ibex_core_with_rf.sv
    if [ "$width" != 32 ]; then
      if [ "$form" = param ]; then
        sed -i "s/^\(  parameter int unsigned            RegFileDataWidth = \)32,/\1$width,/" "$wrapper"
      else
        sed -i "s/^\(    \.DataWidth        (\)RegFileDataWidth),/\1$width),/" "$wrapper"
      fi
      if cmp -s "$wrapper" "$SNAP/PdatScorr/ibex_core_with_rf.sv"; then
        echo "wrapper patch did not apply" >&2
        exit 1
      fi
    fi
    cd "$flow/PdatScorr"
    ;;
  *)
    if [ "$width" != 32 ]; then
      python3 "$HERE/make_narrow_regfile.py" "$IBEX_ROOT/rtl/ibex_register_file_ff.sv" "$width" "$form" \
        "$run/width$w/odc_optimized_rtl/ibex_register_file_ff_optimized.sv"
    fi
    cd "$PSCORR_SYNTHESIS_DIR"
    ;;
esac
./synth_core.sh --core ibex --gates "$HERE/dsl/data_width/width$w.dsl" "$run" > "$OUT/logs/width_${form}_$w.log" 2>&1
