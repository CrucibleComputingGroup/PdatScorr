# Shared native-baseline normalization audit

The declared pre-FPU baseline runs `opt_expr; opt_clean` after slang elaboration.
This audit replayed those two ordinary frontend passes into separate temporary
JSON exports, without changing source, published baseline files, or proof inputs.
It ran no solver or new proof family.

| Stage | Cells | Wires | Literal-x occurrences in cell connections |
|---|---:|---:|---:|
| Raw elaboration | 20,741 | 27,803 | 81,815 |
| After `opt_expr` | 20,741 | 27,803 | 81,815 |
| After `opt_clean` | 17,785 | 17,522 | 81,702 |

The entire parsed JSON before/after `opt_expr` is identical. `opt_clean` removes
2,612 buffer cells and 344 unused cells; the latter include six unused state
cells totaling 73 bits. Thus cleanup is broader than deleting the duplicate
load-write-enable driver alone, but it is ordinary buffer/dead-logic cleanup.
The removed-cell inventory is retained in `summary.json`.

Using only the original buffer connections to resolve aliases, every surviving
cell has identical type, parameters, attributes, port directions, and port
connections. There are no alias conflicts or unmapped surviving connections.
The replayed final JSON exactly equals the published `normalized.json`.
There are no net initialization attributes in either graph.

The 113 fewer literal-x connection occurrences belong to 32 removed cells.
No surviving undefined literal is concretized by this audited normalization.
The count measures repeated literals on cell connections, not unique arbitrary
values or state bits. Many remaining x literals may be on unobservable or
unreachable branches; this audit does not classify their relevance.

The trusted native-hardware baseline is the pinned RTL after declared ordinary
frontend normalization, shared by reference and candidates. This audit does
not prove slang elaboration equivalent to source RTL, and it does not validate
later `prep`, synthesis, or solver export. Preserving the intended meaning of
the remaining undefined values during proof lowering is a separate requirement;
buffer/dead-code cleanup alone is not evidence of unsoundness.

`audit.ys` and `audit.log` retain the exact export command sequence. Large raw,
intermediate, and normalized models remain in the ignored external directory
and are bound by SHA-256 in `summary.json`. The original preparation script,
normalization script/log, and source manifest are copied here. Re-run the
no-solver comparison with `audit_normalization.py --frontend <original frontend>
--exports <audit export directory> --prepare-script <prepare_frontend.py>
--output <new evidence directory>`. `SHA256SUMS` covers this package.
