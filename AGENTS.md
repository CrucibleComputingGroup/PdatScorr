# Project instructions

- The user approved the Pscorr-focused dynamic-scheduling study on 2026-11-04. Proceed with implementation and experiments on a small genuine OoO core; RSD may be replaced. Demonstrate timing/microarchitectural constraints -> automatically proved ODCs -> hardware savings on fixed RTL and capacities. Manual ROB/RS/PRF resizing or hand-written source cuts alone do not establish the contribution. Use the same reset semantics, constraints, observation boundary, and mapping for all method comparisons. Keep new claims out of the manuscript until the mechanism is demonstrated and validated.

- Commit and push completed, validated changes to the relevant review branch so the user can review them; do not leave this as an optional follow-up.
- Keep Pscorr experiment code and evidence in this repository. The manuscript belongs in `Allenjin123/DAC-2026-PSCORR`; keep bulky experiment artifacts outside that Overleaf-linked repository.
- Preserve recorded raw results and provenance. Use new output directories for new experiments, and distinguish local proofs, finite simulation evidence, capacity changes, and automatic optimization results.

- The 0.893% MSHR-component tag optimization is a mechanism/regression test only; the user rejected its magnitude as a paper result. Prioritize substantial automatically removed RS/LSQ storage and measured whole-core impact, with capacities unchanged and lifetime bounds derived from the original constrained system. Do not add the small pilot result to the manuscript.
