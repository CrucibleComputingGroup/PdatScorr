#!/usr/bin/env python3
"""
Add timing constraints to Ibex for enhanced ABC scorr optimization.

This script demonstrates how to programmatically add timing constraints
that help ABC's scorr command achieve better sequential optimization.
"""

import argparse
import re
from typing import List, Tuple
from pathlib import Path

class TimingConstraint:
    """Represents a timing constraint for synthesis."""

    def __init__(self, name: str, signal_from: str, signal_to: str,
                 min_cycles: int, max_cycles: int, condition: str = ""):
        self.name = name
        self.signal_from = signal_from
        self.signal_to = signal_to
        self.min_cycles = min_cycles
        self.max_cycles = max_cycles
        self.condition = condition

    def to_sv(self) -> str:
        """Generate SystemVerilog assumption for this constraint."""
        if self.condition:
            cond = f"rst_ni && {self.condition}"
        else:
            cond = "rst_ni"

        return f"""
  // Timing constraint: {self.name}
  // {self.signal_from} -> {self.signal_to} within [{self.min_cycles}:{self.max_cycles}] cycles
  always_comb begin
    if ({cond}) begin
      assume property (@(posedge clk_i)
        {self.signal_from} |-> ##[{self.min_cycles}:{self.max_cycles}] {self.signal_to});
    end
  end
"""

class IcacheTimingConstraints:
    """Collection of timing constraints for the Ibex icache."""

    def __init__(self, fetch_latency: int = 5, hit_latency: int = 2,
                 miss_latency: int = 10, inval_latency: int = 20):
        self.fetch_latency = fetch_latency
        self.hit_latency = hit_latency
        self.miss_latency = miss_latency
        self.inval_latency = inval_latency

        # Define the constraints
        self.constraints = [
            # Memory interface timing
            TimingConstraint(
                "mem_grant_timing",
                "instr_req_out_o",
                "instr_gnt_i",
                0, fetch_latency,
                "instr_req_out_o"
            ),

            # Cache hit timing (when cache enabled)
            TimingConstraint(
                "cache_hit_timing",
                "(instr_req_o && icache_en_i && !icache_busy)",
                "instr_valid_i",
                0, hit_latency,
                "icache_en_i"
            ),

            # Cache miss timing
            TimingConstraint(
                "cache_miss_timing",
                "(instr_req_o && (!icache_en_i || cache_miss))",
                "instr_valid_i",
                hit_latency, miss_latency,
                ""
            ),

            # Cache invalidation timing
            TimingConstraint(
                "cache_inval_timing",
                "icache_inval_i",
                "!icache_busy",
                1, inval_latency,
                ""
            ),
        ]

    def generate_sv(self) -> str:
        """Generate complete SystemVerilog constraint block."""
        sv_code = """
// ==========================================
// ICache Timing Constraints for Synthesis
// ==========================================
// These constraints help ABC scorr optimize sequential logic
// by providing information about timing relationships

`define ICACHE_FETCH_LATENCY {fetch_lat}
`define ICACHE_HIT_LATENCY   {hit_lat}
`define ICACHE_MISS_LATENCY  {miss_lat}
`define ICACHE_INVAL_LATENCY {inval_lat}
""".format(
            fetch_lat=self.fetch_latency,
            hit_lat=self.hit_latency,
            miss_lat=self.miss_latency,
            inval_lat=self.inval_latency
        )

        # Add each constraint
        for constraint in self.constraints:
            sv_code += constraint.to_sv()

        # Add sequential depth properties for scorr
        sv_code += self._generate_sequential_depth_hints()

        return sv_code

    def _generate_sequential_depth_hints(self) -> str:
        """Generate hints about sequential depth for scorr."""
        return f"""
  // ==========================================
  // Sequential Depth Hints for scorr
  // ==========================================
  // These properties help ABC understand the pipeline depth

  // Overall pipeline depth from request to response
  property icache_pipeline_depth;
    @(posedge clk_i) disable iff (!rst_ni)
    instr_req_out_o |-> ##[1:`ICACHE_FETCH_LATENCY] instr_rvalid_i;
  endproperty
  pipeline_depth_assume: assume property (icache_pipeline_depth);

  // Cache state machine maximum cycles
  property cache_state_cycles;
    @(posedge clk_i) disable iff (!rst_ni)
    icache_busy |-> ##[1:`ICACHE_INVAL_LATENCY] !icache_busy;
  endproperty
  cache_state_assume: assume property (cache_state_cycles);

  // Memory response ordering (pipelined slave)
  logic [3:0] req_counter, resp_counter;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_counter <= 4'b0;
      resp_counter <= 4'b0;
    end else begin
      req_counter <= req_counter + (instr_req_out_o & instr_gnt_i);
      resp_counter <= resp_counter + instr_rvalid_i;
    end
  end

  // Responses must eventually arrive for all requests
  always_comb begin
    if (rst_ni) begin
      assume property (@(posedge clk_i)
        (req_counter > resp_counter) |->
        ##[1:`ICACHE_FETCH_LATENCY] (resp_counter >= $past(req_counter)));
    end
  end
"""

def inject_constraints_into_module(
    module_path: str,
    constraints_sv: str,
    output_path: str,
    module_name: str = "ibex_core"
) -> bool:
    """Inject timing constraints into a Verilog module."""

    with open(module_path, 'r') as f:
        content = f.read()

    # Find the module and endmodule
    module_pattern = rf'module\s+{module_name}\s*[^;]*;'
    endmodule_pattern = r'endmodule'

    # Find last endmodule
    endmodule_match = list(re.finditer(endmodule_pattern, content))
    if not endmodule_match:
        print(f"ERROR: Could not find 'endmodule' in {module_path}")
        return False

    last_endmodule_pos = endmodule_match[-1].start()

    # Inject constraints before endmodule
    modified = (
        content[:last_endmodule_pos] +
        "\n" + constraints_sv + "\n" +
        content[last_endmodule_pos:]
    )

    # Write output
    with open(output_path, 'w') as f:
        f.write(modified)

    print(f"Successfully injected constraints into {output_path}")
    return True

def generate_abc_script(
    aiger_input: str,
    aiger_output: str,
    k_depth: int = 3,
    use_constraints: bool = True
) -> str:
    """Generate ABC script for scorr with timing constraints."""

    script = f"""# ABC script for sequential optimization with timing constraints
read_aiger {aiger_input}
print_stats

# Structural hashing
strash
print_stats

# Detect and merge sequential equivalences
# -c: use constraints (timing assumptions)
# -F {k_depth}: k-induction depth (should match max latency)
# -C 10000: conflict limit
# -v: verbose output
"""

    if use_constraints:
        script += f"""
# Run scorr with constraints enabled
cycle 100
scorr -c -F {k_depth} -C 10000 -v
"""
    else:
        script += f"""
# Run scorr without constraints (for comparison)
scorr -F {k_depth} -C 10000 -v
"""

    script += f"""
print_stats

# Additional optimizations
dc2
dretime
print_stats

# Write optimized design
write_aiger {aiger_output}
quit
"""
    return script

def analyze_constraint_impact(
    pre_abc_aig: str,
    post_abc_aig: str
) -> dict:
    """Analyze the impact of timing constraints on optimization."""

    import subprocess
    import re

    def get_aig_stats(aig_file):
        """Get statistics from an AIG file using ABC."""
        try:
            result = subprocess.run(
                ['abc', '-c', f'read_aiger {aig_file}; print_stats'],
                capture_output=True, text=True
            )
            output = result.stdout

            # Parse statistics
            stats = {}
            # Look for: i/o = X/ Y
            io_match = re.search(r'i/o\s*=\s*(\d+)/\s*(\d+)', output)
            if io_match:
                stats['inputs'] = int(io_match.group(1))
                stats['outputs'] = int(io_match.group(2))

            # Look for: lat = X
            lat_match = re.search(r'lat\s*=\s*(\d+)', output)
            if lat_match:
                stats['latches'] = int(lat_match.group(1))

            # Look for: and = X
            and_match = re.search(r'and\s*=\s*(\d+)', output)
            if and_match:
                stats['and_gates'] = int(and_match.group(1))

            # Look for constraints
            const_match = re.search(r'constraint\s*=\s*(\d+)', output)
            if const_match:
                stats['constraints'] = int(const_match.group(1))

            return stats
        except Exception as e:
            print(f"Error analyzing {aig_file}: {e}")
            return {}

    pre_stats = get_aig_stats(pre_abc_aig)
    post_stats = get_aig_stats(post_abc_aig)

    # Calculate improvements
    improvements = {}
    if pre_stats and post_stats:
        if 'and_gates' in pre_stats and 'and_gates' in post_stats:
            pre_gates = pre_stats['and_gates']
            post_gates = post_stats['and_gates']
            improvements['gate_reduction'] = {
                'before': pre_gates,
                'after': post_gates,
                'reduction_pct': round(100 * (1 - post_gates/pre_gates), 2)
            }

        if 'latches' in pre_stats and 'latches' in post_stats:
            pre_latches = pre_stats['latches']
            post_latches = post_stats['latches']
            improvements['latch_reduction'] = {
                'before': pre_latches,
                'after': post_latches,
                'reduction_pct': round(100 * (1 - post_latches/pre_latches), 2)
            }

    return {
        'pre_abc': pre_stats,
        'post_abc': post_stats,
        'improvements': improvements
    }

def main():
    parser = argparse.ArgumentParser(
        description='Add timing constraints to Ibex for better scorr optimization'
    )
    parser.add_argument(
        'module_file',
        help='Path to the Verilog module to constrain (e.g., ibex_core.sv)'
    )
    parser.add_argument(
        '-o', '--output',
        default='ibex_core_timed.sv',
        help='Output file with timing constraints'
    )
    parser.add_argument(
        '--fetch-latency',
        type=int, default=5,
        help='Maximum instruction fetch latency (default: 5)'
    )
    parser.add_argument(
        '--hit-latency',
        type=int, default=2,
        help='Cache hit latency (default: 2)'
    )
    parser.add_argument(
        '--miss-latency',
        type=int, default=10,
        help='Cache miss latency (default: 10)'
    )
    parser.add_argument(
        '--inval-latency',
        type=int, default=20,
        help='Cache invalidation latency (default: 20)'
    )
    parser.add_argument(
        '--abc-depth',
        type=int, default=3,
        help='ABC scorr k-induction depth (default: 3)'
    )
    parser.add_argument(
        '--analyze',
        nargs=2,
        metavar=('PRE_AIG', 'POST_AIG'),
        help='Analyze impact of constraints on two AIG files'
    )

    args = parser.parse_args()

    if args.analyze:
        # Analyze existing AIG files
        print("Analyzing constraint impact...")
        results = analyze_constraint_impact(args.analyze[0], args.analyze[1])

        print("\n=== Constraint Impact Analysis ===")
        print(f"Pre-ABC stats: {results['pre_abc']}")
        print(f"Post-ABC stats: {results['post_abc']}")

        if results['improvements']:
            print("\n=== Improvements ===")
            for metric, data in results['improvements'].items():
                print(f"{metric}:")
                print(f"  Before: {data['before']}")
                print(f"  After: {data['after']}")
                print(f"  Reduction: {data['reduction_pct']}%")
    else:
        # Generate and inject constraints
        print("Generating timing constraints...")
        print(f"  Fetch latency: {args.fetch_latency} cycles")
        print(f"  Hit latency: {args.hit_latency} cycles")
        print(f"  Miss latency: {args.miss_latency} cycles")
        print(f"  Invalidation latency: {args.inval_latency} cycles")

        # Create constraints
        icache_constraints = IcacheTimingConstraints(
            fetch_latency=args.fetch_latency,
            hit_latency=args.hit_latency,
            miss_latency=args.miss_latency,
            inval_latency=args.inval_latency
        )

        constraints_sv = icache_constraints.generate_sv()

        # Save constraints to separate file
        constraints_file = args.output.replace('.sv', '_constraints.sv')
        with open(constraints_file, 'w') as f:
            f.write(constraints_sv)
        print(f"Saved constraints to {constraints_file}")

        # Inject into module
        if inject_constraints_into_module(
            args.module_file,
            constraints_sv,
            args.output
        ):
            print(f"\n✓ Successfully created {args.output}")

            # Generate ABC script
            abc_script_file = args.output.replace('.sv', '_abc.scr')
            abc_script = generate_abc_script(
                'design_pre_abc.aig',
                'design_post_abc.aig',
                k_depth=args.abc_depth,
                use_constraints=True
            )

            with open(abc_script_file, 'w') as f:
                f.write(abc_script)
            print(f"✓ Generated ABC script: {abc_script_file}")

            print(f"\nNext steps:")
            print(f"1. Synthesize {args.output} to AIGER format")
            print(f"2. Run ABC with: abc -f {abc_script_file}")
            print(f"3. Analyze results with: {__file__} --analyze pre.aig post.aig")

if __name__ == '__main__':
    main()