# SourceChangeShape returned text field is corrupted under the retained native producer

Status: OPEN. Inference-only causation is not established; the explicit nominal control also fails.

Producer: admitted historical Stage 2 SHA-256 `a4e44d0999f5cb0a50882c0e3b828e65e98351a541bef81c93892de0cfd1b5c6`. Source base: `7f445e481c2e2ebdff3ef7e1b0aa70a49beca45b` plus the owned contracts/cases. Three native builds succeeded with no stub fallback, closed process-tree receipts, and preserved producer/entry caches.

The empty valid event case must return `SourceChangeShapeV1(valid: true, reason: "well_formed_change_batch")`. The first probe exits 1 before any case passes. Instrumentation observes valid=true, but reason prints `1`. Importing the return type and annotating the receiving value still produces valid=true with an empty reason; its additional inferred control remains broken. Thus this is not repaired by the explicit nominal control. Root cause remains unresolved across constructor/return metadata, transport and field projection; do not assert a caller-inference-only fix.

Evidence: `build/native_probe/source-contracts-v1/cycle1/`, `cycle2/`, final `run.log`, `cycle3-run-counts.json` and `cycle3-identity.json`. All have zero observed case passes. The independent `test/fixtures/compiler/source_change_return_field_inference_probe.spl` is an authored reproducer, UNRUN separately; the observed failing call is retained in the shared native probe.

The native harness marks its explicit type/import control as a workaround diagnostic and remains failing. Common contracts and five SSpec scenarios are not qualified. Fix or requalify field transport on a current immutable producer, then execute the actual cases once. Do not change record widths or result semantics merely to make this historical producer pass.

## Retained HIR symbol metadata inspection

The historical producer's retained contracts entry
`d8429deef61f247ca820718d5c123b2c946c963839b93fe19bdc75d893a487a4.hir`
has 11,490 lines, zero integer `3` tokens and 105 `N` tokens. The scope
symbol maps encode `SourceChangeShapeV1` followed by `N` at lines
2488/2489, 2959/2960 and 3123/3124. The struct declaration encodes a present
symbol with ID `N` at line 10248, immediately before its name and two-field
list. The generated codec writes scope symbol IDs through put_i64 and
decodes `N` as nil; these are not optional text/documentation fields.

This matches the documented old staged-native serializer defect in
[hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md](hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md), whose source
fix is already present in current release. The historical producer also
writes the old W-only cache frame rather than the current checksum envelope.
A newer source tree does not repair that frozen producer's own serializer.

This proves malformed persisted symbol metadata in the retained artifact.
It does not prove that a cache load caused the returned-field failure, or
that fixing the codec alone fixes constructor/return/projection behavior.
No source widths, exports or result semantics were changed; no fourth native
retry was performed. Inspection provenance is retained in
`build/native_probe/source-contracts-v1/retained-hir-symbol-inspection.json`.

Next qualification must use a newly admitted producer with the codec fix and
intact symbol IDs, retain fresh/warm cache identities, then establish actual
returned fields and real case counts. Full CLI/TestRunner qualification and
authenticated review admission remain required before this draft can land.
