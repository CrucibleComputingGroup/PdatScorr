# Delta-only reset-cube import

`reset_cube_import.py` composes the closed 42-word/583-bit cube with the completed register-status native query. It applies only the proved constant delta to the **current** graph. The cube's older `6192d7a4…` graph is used to validate its source certificate and is never substituted wholesale into the newer query.

The importer requires the completed independent cube review, the exact property-free cube source `bb52d686…`, and the frozen 48-premise reference preparation at `build/harvard_rom_register_status_native_prepare_v1`. It validates that preparation's native export, harness, final query/AIG/property inventory, and complete proof dependencies. The fresh caller must supply its four closed word/ROM/inactive/register-status records and the actual current harness/native descriptor. Their hashes must match the reference environment and native export, and every transitive proof dependency is checked.

The current graph is reconstructed from the cube's source using the separately proved 275 register-status constants, the original seven word conclusions, 40 destination-field conclusions, and two unchanged ALU observation ports. Both predicate families are regenerated from their source bindings; their exact 119 and 360 encoding cells must match the current graph. This establishes that the only intervening native change is the already-proved, disjoint register-status substitution.

The selected 583 native Q bits are disjoint from those 275 bits, the prior 1761 reset bits, and every existing predicate connection. Each selected FF must still equal its original source primitive. The importer removes those 42 whole words and replaces only their proved constant fanout, then audits every graph object and connection. All 479 predicate cells, 47 derived assumptions, native/probe ports, prior register-status facts, and arithmetic equations remain intact. It explicitly checks removal of the eight MUL/DIV CDB-arbiter state bits retained in the earlier proof abstraction.

Both final source-native proof projections are rebuilt exactly. The whitelisted symbolization, binary-choice exposure, and preparation exports are replayed, and all generated models must match the proved models **byte for byte**. No SAT solver is rerun. The original source-bound SAT scripts, passed logs, reset-base premise, and joint induction target are checked. The import adds no assumption and no new environment restriction. It preserves the original whole-query three assertions/48 assumptions after the unchanged harness is added.

The API is:

```python
query, record = import_reset_cube(
    cube_run, reference_prepared, current_query, output,
    yosys=yosys,
    current_records={
        "native_word_domain_import": word_record,
        "external_rom_domain_import": rom_record,
        "inactive_fu_import": inactive_record,
        "register_status_import": register_record,
    },
    current_harness=harness_path,
    current_native_core=native_core_json,
)
```

Call `verify_dependencies(record)` after any subsequent query or preparation. The caller should merge this map into its existing transitive dependency closure. The physical/native export remains separate and unchanged. The new graph is a proof-only model, not a hardware candidate or an admission result.

Five focused tests passed in 39.84 seconds. The positive test performs the actual two export replays and checks all preserved predicates, probes, constants, and arbitration bits. Negative tests reject a missing independent review, wholesale replacement with the older cube graph, a changed derived predicate, and a mutated transitive proof log. No test invokes SAT or a full-core solver:

```bash
python -m pytest -q tests/unit/test_reset_cube_import.py
```

The initial implementation does not edit `formal_screen.py`; its owner integrates an explicit opt-in flag for a separately recorded combined preparation. Any later solver run needs its own authorization and source-bound validator for this preparation family.
