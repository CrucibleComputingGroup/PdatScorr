# Native word theorem import review

The reviewed `domain_lemmas.py` imports seven conclusions proved on the original native instruction data path: six stored words and the decoder input. The exact source slices, all 36 retained control cells, and the entire theorem harness are reconstructed. The stored conclusions are unconditional; their proof uses initial native reset and a reset-qualified valid-response alphabet premise. Reapplying a reset guard to the conclusions is unnecessary.

The importer replays the frozen decoder certifier and regenerates the small projection model without rerunning the solver. Exact JSON and SMT agreement binds the successful base/induction logs to the reconstructed property. It rejects bounded-only results, altered source controls, changed Q bindings, extra theorem outputs, modified assumptions, and proof dependency changes.

The seven derived assumptions are sound only when the external response-domain premise is discharged in the new context. The composed query separately validates the source-identical Harvard ROM producer theorem, which exposes all core outputs as arbitrary inputs and retains the original initial-reset premise. No admission, occupancy, readiness, tag-ownership, or arithmetic assumption is added.

No concrete soundness blocker was found in this source review. It is not an independent rerun of the original solver proofs, an admission certificate, or authorization for storage removal. The exact reviewed source hash is recorded in `review.json`.
