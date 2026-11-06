# Original structured diagnostics for immutable source checking

Status: authored, runtime NOT_RUN. This is an additive compiler-owner change for the selected source-snapshot/LSP overlay contract, not a replacement CLI diagnostic format.

`DiagnosticV1` is the canonical rich record. `CompileResult` remains compatible: existing variants and text payloads are unchanged. `CompileContext` holds original records only after the snapshot API calls `begin_structured_collection_v1`. The compiler-owned source result can then return these records alongside its immutable source receipt. Normal builds retain their text behavior without retaining a second full diagnostic collection.

## Actual producers and capture

| Producer | Capture boundary | Information preserved |
| --- | --- | --- |
| Core parser | Original parser error/warning methods; ParserState snapshot and driver retained-source drain | Original source path and byte/line/column span; warnings also survive successful parses. No parsing of formatted error text. |
| HM inference | `types/type_infer/diagnostic_v1.spl`, called from `hir_typecheck_consumer_v1.spl` before formatting | Typed error variant, actual span, cross-file related type labels, dimension notes/help and resolved driver severity. No retained HIR/type roots. |
| HIR frontend lint | Original `HirFrontendFinding` now carries its emitted span | Original code/message/span and warning-first policy; absent locations remain absent. |
| Visibility | Original `VisibilityWarning` consumed before formatting | Original code/message/span and resolved driver severity. |
| Existing rich record | `CompileContext.capture_diagnostics_v1` | Entire value including nested children, labels, notes, help, macro expansion chain and fixes. No downgrade to a message-only reconstruction. |

Stable HM record codes are selected from the typed error variant. The function-value/data-slot error keeps E-TYPE-FN-VALUE and original mismatch labels. Missing source locations are not invented. Existing CLI strings are still rendered through their prior formatting function.

`capture_diagnostics_v1(records, covered_errors, covered_warnings)` covers existing compatibility entries. Counts need not equal record count: multiple original parser diagnostics may correspond to one legacy module-error string. Invalid counts or the8192 retained-record bound invalidate complete collection. String-only infrastructure failures are never covered merely because a parser also emitted an error. Error-return capture additionally requires a fresh parser generation, exact source identity and the canonical parser-error identity; otherwise records remain partial with the infrastructure error uncollected.

## Completion and lifetime

An empty list is not evidence of a clean check. `source_analysis_diagnostics_collected_v1(require_typecheck=true)` requires collection enabled, intact compatibility/capture counts, no uncaptured producer or invalid capture, actual parser completion for every admitted source path, and actual HM expected/completed module inventories. The API may omit the HM requirement only for a ParseError result. Parser and HM completion receipts exist even when no diagnostic was emitted.

The actual HM pass records its expected module identities at entry; completed receipts come from the actual typed consumer. Advisory-only messages from an unmigrated producer also invalidate completeness. Direct legacy warning pushes are detected through array totals. A failed/disabled/missing producer cannot become Completed with zero findings.

`session_kept_values_v1` retains the original structured array and flat parser/HM inventories, plus snapshot-provider/provenance values. The archive-body typecheck lease explicitly promotes the structured receipt before ending scratch. Full HIR bodies are not retained just to verify diagnostic collection. Recursive record survival through real session teardown remains an executable qualification gate, not a static proof.

## Open producer coverage

CFG declaration diagnostics, semantic/safety/representation receipt producers and infrastructure/borrow paths still include string-only emissions. Their messages/counts invalidate complete collection rather than being reconstructed from logs. Snapshot mode disables archive/streaming reuse; other worker/shard string-wire paths are not promoted into complete snapshot evidence. Migrating these original producers is still required where the selected full check contract encounters them.

Exact coverage/fidelity tests are authored in `test/01_unit/compiler/driver/structured_diagnostic_capture_v1_spec.spl`; parser snapshot and immutable-driver integration specs belong to their adjacent owners. Runtime admission must include warning/error cases, multi-file ranges, cache/reset isolation and post-session access on the approved self-hosted runtime. No tests were executed for this implementation.
