# Ablation Study: Cache Timing Constraint Optimization

## Purpose

Test different post-cone extraction strategies to minimize constraint hardware overhead while maintaining optimization benefits.

## Problem Statement

Cache-aware timing constraints add ~20 flip-flops for tracking memory access patterns. After ABC's `scorr -c` optimization, we use `cone` to extract only real outputs (removing constraint outputs). However, constraint hardware may remain in the final circuit if not properly cleaned up.

## Hypothesis

Different ABC optimization sequences after `cone` extraction may better remove constraint-related hardware.

## Test Configurations

### Baseline
- **ISA-only**: No timing constraints (reference)
- **baseline**: `cone -O 0 -R OUTPUTS` (cone extraction only, no post-processing)

### Test Configurations (Measure combinations)

**Measure 1: BLIF Round-trip**
- `write_blif` → `read_blif` before cone
- Theory: Forces circuit re-optimization, may break constraint dependencies

**Measure 2: ABC Depth**
- Test depths: 2, 4, 6, 8
- Theory: Higher k-induction may find more equivalences

**Measure 3: Combinational Optimization After Cone**
- `fraig`: Functionally-reduced AIG
- `dc2`: Don't-care optimization
- `dretime`: Retiming
- `strash`: Structural hashing

**Configurations:**

| Config | Strategy |
|--------|----------|
| configA | write_blif → read_blif → cone |
| configB | cone → fraig |
| configC | cone → dc2 |
| configD | cone → dretime |
| configE | cone → fraig → dc2 |
| configF | cone → fraig → dc2 → dretime |
| configG | write_blif → read_blif → cone → fraig → dc2 → dretime |
| configH | cone → strash → fraig → dc2 |

## Scripts

### Option 1: Full Ablation (Slower, Complete)
```bash
./ablation_cache_timing.sh [dsl_file] [output_dir]
```

Runs full synthesis pipeline for each configuration:
- Generates ISA constraints
- Adds cache timing constraints
- Runs Synlig → ABC scorr → different post-cone strategies
- Synthesizes to gates for area measurement

**Pros**: Complete test from scratch
**Cons**: Slow (~30-60 min for all configs × all depths)

### Option 2: Post-Cone Only (Faster, Focused)
```bash
./ablation_postcone.sh [dsl_file]
```

Reuses pre-computed scorr-optimized files:
- Runs baseline + cache_timing synthesis once
- Tests only the post-cone extraction phase
- Much faster iteration

**Pros**: Fast (~5-10 min), isolates the post-cone question
**Cons**: Requires running synthesis first

## Usage

### Recommended Workflow:

```bash
# Run the faster post-cone ablation
./ablation_postcone.sh ../PdatDsl/examples/rv32im.dsl

# Results saved to: output/ablation_TIMESTAMP/
# - results.csv: Machine-readable data
# - ablation_summary.txt: Human-readable report
```

### Cleanup:

```bash
# Remove all ablation test files
rm -rf output/ablation_*
rm -f ablation_*.sh ABLATION_STUDY.md
```

## Expected Output

### Results CSV Format:
```csv
Config,Depth,Type,PreCone_Gates,PostCone_Gates,ChipArea_um2,Strategy
isa_baseline,4,isa_only,N/A,N/A,49094.58,ISA constraints only
baseline,4,cache_timing,17428,17428,49990.44,"cone -O 0 -R 431"
configA_blif_cone,4,cache_timing,17428,17350,49850.12,"write_blif..."
...
```

### Analysis Questions:

1. **Does BLIF round-trip help?** Compare configA vs baseline
2. **Which combo-opt is best?** Compare configB, C, D, E, F, G, H
3. **Is there depth dependency?** Check if best config varies by depth
4. **Can we beat ISA-only?** Any config with area < baseline?

## Success Criteria

**Ideal**: Find a post-cone strategy where cache timing produces **equal or better area** than ISA-only baseline, proving that constraint hardware is fully removed and optimization benefits are real.

**Acceptable**: Find best strategy that minimizes overhead, even if small overhead remains.

**Failure**: All strategies show >1% overhead, suggesting conditional assumes are fundamentally incompatible with clean separation.

## Next Steps Based on Results

- **If successful**: Update `synth_ibex_with_cache_timing.sh` with winning strategy
- **If marginal**: Simplify cache timing to unconditional assumes
- **If failed**: Abandon cache-aware timing, stick with simple uniform bounds
