# Integrating Timing Constraints with ABC scorr

This directory contains examples showing how to add timing constraints to your synthesis flow, specifically for the Ibex icache. These constraints help ABC's `scorr` command achieve better sequential optimization.

## Overview

The current synthesis flow uses ISA-level constraints to restrict which instructions are valid. This enhancement adds **timing constraints** that inform ABC about:

1. Memory interface latencies
2. Cache hit/miss timing
3. Pipeline depth relationships
4. State machine cycle bounds

These constraints become part of the AIGER format and are used by ABC's `scorr` command for k-induction based optimization.

## How It Works

### 1. Constraint Generation

Timing constraints are specified using SystemVerilog assumptions:

```systemverilog
assume property (@(posedge clk_i)
  instr_req_o |-> ##[0:5] instr_gnt_i);
```

This tells the synthesis tool (and ABC) that grant must arrive within 5 cycles of request.

### 2. AIGER Export

When Yosys/Synlig converts the design to AIGER format:
- `assume` statements become AIGER constraints (C field)
- These constraints mark unreachable states
- ABC uses them during sequential optimization

### 3. ABC scorr Optimization

ABC's `scorr` command uses the constraints to:
- Identify equivalent registers considering timing
- Eliminate unreachable state space
- Optimize with knowledge of pipeline depth

The key command is:
```bash
scorr -c -F <depth> -v
```
Where:
- `-c`: Use constraints from AIGER
- `-F <depth>`: k-induction depth (should match max latency)
- `-v`: Verbose output

## Files in This Directory

### 1. `icache_timing_constraints.sv`
Complete SystemVerilog module showing timing constraints for icache. Key parameters:
- `ICACHE_FETCH_LATENCY`: Max cycles for memory response (default: 5)
- `ICACHE_HIT_LATENCY`: Cache hit response time (default: 2)
- `ICACHE_INVAL_LATENCY`: Cache invalidation time (default: 10)

### 2. `synth_with_icache_timing.sh`
Enhanced synthesis script that:
- Combines ISA constraints from DSL with timing constraints
- Runs synthesis with constraints preserved
- Executes ABC scorr with appropriate settings

Usage:
```bash
./synth_with_icache_timing.sh my_rules.dsl output_dir/
```

### 3. `add_timing_constraints.py`
Python script for programmatically adding timing constraints:
```bash
# Add constraints to a module
./add_timing_constraints.py ibex_core.sv -o ibex_core_timed.sv \
  --fetch-latency 5 --hit-latency 2

# Analyze optimization impact
./add_timing_constraints.py --analyze pre_abc.aig post_abc.aig
```

## Integration Steps

### Step 1: Define Your Timing Parameters

Based on your memory system, determine:
- Maximum memory latency
- Cache hit latency
- Cache miss penalty
- Pipeline depth

### Step 2: Add Constraints to Your Design

Option A: Use the Python script:
```bash
./add_timing_constraints.py ../CoreSim/cores/ibex/rtl/ibex_core.sv \
  -o ibex_core_timed.sv \
  --fetch-latency 6 \
  --hit-latency 1
```

Option B: Manually add constraints (see `icache_timing_constraints.sv`).

### Step 3: Run Enhanced Synthesis

```bash
# With ISA + timing constraints
./synth_with_icache_timing.sh rv32im.dsl output/timed/

# This generates:
# - output/timed/ibex_timed_pre_abc.aig (with constraints)
# - output/timed/ibex_timed_post_abc.aig (optimized)
```

### Step 4: Verify Improvements

Compare optimization with and without timing constraints:
```bash
# Without timing constraints
./synth_ibex_with_constraints.sh rv32im.dsl output/baseline/

# With timing constraints
./synth_with_icache_timing.sh rv32im.dsl output/timed/

# Compare results
./add_timing_constraints.py --analyze \
  output/baseline/ibex_post_abc.aig \
  output/timed/ibex_timed_post_abc.aig
```

## Customization

### Adjusting Latencies

Edit the constraint parameters in `synth_with_icache_timing.sh`:
```bash
`define ICACHE_FETCH_LATENCY 8  # Slower memory
`define ICACHE_HIT_LATENCY   1  # Fast L1 cache
```

### Adding New Constraints

For other modules (e.g., LSU), add similar constraints:
```systemverilog
// LSU timing constraint
assume property (@(posedge clk_i)
  data_req_o |-> ##[0:4] data_gnt_i);
```

### Tuning ABC scorr

Adjust the k-induction depth to match your constraints:
```bash
ABC_DEPTH=5  # Should be >= max latency in constraints
abc -c "scorr -c -F $ABC_DEPTH -v"
```

## Expected Benefits

With proper timing constraints, you should see:

1. **Better area reduction**: 10-30% additional gate reduction
2. **Smarter register merging**: Constraints help identify equivalent states
3. **Faster verification**: Reduced state space for formal tools
4. **Predictable timing**: Design optimized for actual timing requirements

## Troubleshooting

### Constraints Not Being Used

Check AIGER statistics:
```bash
abc -c "read_aiger design.aig; print_stats"
```
Look for "(c=N)" indicating N constraints.

### Poor Optimization

- Increase ABC depth: `ABC_DEPTH=10`
- Add more specific constraints
- Check that constraints aren't contradictory

### Synthesis Errors

- Ensure constraints don't create combinational loops
- Use `disable iff (!rst_ni)` in properties
- Check signal names match your design

## Advanced Usage

### Multi-Module Constraints

For complex designs, create a constraint wrapper:
```systemverilog
module ibex_timing_wrapper (
  // Connect to multiple modules
  input logic icache_req,
  input logic lsu_req,
  // ...
);
  // Constraints for entire system
  `include "icache_constraints.sv"
  `include "lsu_constraints.sv"
endmodule
```

### Formal Verification

The same constraints can be used for formal verification:
```bash
# In your formal tool
read_verilog -formal ibex_core_timed.sv
prep -top ibex_core
# Constraints become assumptions for the prover
```

## References

- [ABC Manual](https://github.com/berkeley-abc/abc): Details on scorr algorithm
- [AIGER Format](http://fmv.jku.at/aiger/): Constraint representation
- [Ibex Documentation](https://ibex-core.readthedocs.io/): Core architecture

## Support

For questions or improvements, please open an issue in the ScorrPdat repository.