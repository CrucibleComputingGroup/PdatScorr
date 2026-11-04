#!/usr/bin/env bash
# Build the exact Verilator revision used by build_simulations.py, locally.
set -euo pipefail
experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
tool_dir="$experiment_dir/tools/verilator-4.228"
mkdir -p "$experiment_dir/tools" "$experiment_dir/results"
if [[ ! -d "$tool_dir/.git" ]]; then
    git clone --depth 1 --branch v4.228 https://github.com/verilator/verilator "$tool_dir"
fi
test "$(git -C "$tool_dir" rev-parse HEAD)" = 746c7ea8f786e1183f15c28727cbc0c44e9b556e
# The user's default PATH puts the RISC-V assembler ahead of the host assembler.
export PATH=/usr/bin:/bin:/usr/local/bin
cd "$tool_dir"
autoconf
for log_name in verilator_configure.log verilator_build.log; do
    if [[ -f "$experiment_dir/results/$log_name" ]]; then
        mv "$experiment_dir/results/$log_name" "$experiment_dir/results/${log_name%.log}_previous_$(date +%s%N).log"
    fi
done
./configure > "$experiment_dir/results/verilator_configure.log" 2>&1
make -j12 > "$experiment_dir/results/verilator_build.log" 2>&1
./bin/verilator --version
