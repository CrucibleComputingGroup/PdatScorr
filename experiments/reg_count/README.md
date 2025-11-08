# Register Count Experiment

This experiment measures the impact of register file size on synthesized circuit area.

## Experiment Design

We synthesize the Ibex core with RV32I ISA but varying the number of allowed registers:

| File | Registers | Constraint | Description |
|------|-----------|------------|-------------|
| `04regs.dsl` | x0-x3 (4 regs) | `forbid x4-x31` | Minimal register set |
| `08regs.dsl` | x0-x7 (8 regs) | `forbid x8-x31` | Half of RV32E |
| `16regs.dsl` | x0-x15 (16 regs) | `forbid x16-x31` | RV32E standard |
| `32regs.dsl` | x0-x31 (32 regs) | None | RV32I baseline |

## Hypothesis

Reducing the register file size should reduce circuit area by:
1. **Direct savings**: Smaller register file (fewer flip-flops)
2. **Optimization opportunities**: Register field constraints enable ABC to optimize:
   - Decoder logic (fewer address bits matter)
   - Multiplexer logic (fewer select lines)
   - Dead code elimination in register addressing paths

## Expected Results

We expect to see:
- **Linear reduction** in register file area (proportional to register count)
- **Non-linear reduction** in total core area due to secondary optimizations
- **Diminishing returns** as we approach the minimum (4 registers may not be practical)

## Expected Results

- **AND gate count** (after ABC optimization)
- **Flip-flop count** (register file size)
- **Total cell area** (if gate-level synthesis was used)

As register count decreases, we should see both direct register file savings
and secondary optimizations in decoder/multiplexer logic.

## Integration with Other Projects

This experiment uses the new **AIG-based constraint system** where register
constraints are represented as And-Inverter Graphs. For example:

- `forbid x16-x31` generates: `~rd[4] & ~rs1[4] & ~rs2[4]`
  (MSB of register fields must be 0)

This enables optimal constraint propagation through ABC's sequential
optimization passes.
