# SourceChangeShape returned text field is corrupted under the retained native producer

Status: OPEN. Inference-only causation is not established; the explicit nominal control also fails.

Producer: admitted historical Stage 2 SHA-256 `a4e44d0999f5cb0a50882c0e3b828e65e98351a541bef81c93892de0cfd1b5c6`. Source base: `7f445e481c2e2ebdff3ef7e1b0aa70a49beca45b` plus the owned contracts/cases. Three native builds succeeded with no stub fallback, closed process-tree receipts, and preserved producer/entry caches.

The empty valid event case must return `SourceChangeShapeV1(valid: true, reason: "well_formed_change_batch")`. The first probe exits 1 before any case passes. Instrumentation observes valid=true, but reason prints `1`. Importing the return type and annotating the receiving value still produces valid=true with an empty reason; its additional inferred control remains broken. Thus this is not repaired by the explicit nominal control. Root cause remains unresolved across constructor/return metadata, transport and field projection; do not assert a caller-inference-only fix.

Evidence: `build/native_probe/source-contracts-v1/cycle1/`, `cycle2/`, final `run.log`, `cycle3-run-counts.json` and `cycle3-identity.json`. All have zero observed case passes. The independent `test/fixtures/compiler/source_change_return_field_inference_probe.spl` is an authored reproducer, UNRUN separately; the observed failing call is retained in the shared native probe.

The native harness marks its explicit type/import control as a workaround diagnostic and remains failing. Common contracts and five SSpec scenarios are not qualified. Fix or requalify field transport on a current immutable producer, then execute the actual cases once. Do not change record widths or result semantics merely to make this historical producer pass.
