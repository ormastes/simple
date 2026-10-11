# Imported Result Err record loses provider field ownership

Status: OPEN. Severity: P1. Source repair and regressions are authored; native and compiled-spec qualification are UNEXECUTED.

## Observed failure

Actual producer `892b220e19b5cbafd620190c95b9a2f26fc5ebc08304b8b07d4475da0ea7abb0`, source `b58baa89e4d65a40768fceaf8221fdbdbe58da24`, Redis ELF `a4c2c23d12a4a75132a82de4e8697d3fc1783065262b2f0b8e1ed21e36fbc974` extracts `Err(e)` then reads offset zero and calls `rt_raw_i64_to_string` for `e.message`. The provider stores `IoError.message:text` at offset eight. The actual source is `val r = server.run(...); match r: case Err(e): ... e.message`; the consumer does not import IoError.

Evidence: `redis-startup-failure-contract-ledger.json` (33480434b9c81e9f4c84f81dc3602e8d2775e4f49933fd98e2ffce1182bcf812), and `redis-ioerror-field-provenance-source-diagnosis.json` (7adcb00b9d94f363e196463d4c58c0df0fa8615a139c4faf60cddc9f8b1bc76d), in the retained 20261011 phase2 CUDA-owner artifact directory. This source defect is separate from Redis tagged-text FFI and bind/listen defects.

## Cause and bounded repair

The provider return-shape prescan kept Result Ok identity but discarded Err identity. Safe payload-owner lookup accepts only Ok/Some and only direct calls; it cannot recover an aliased Err value. The legacy fallback can consult a numeric Named ID in the wrong module or the closure-global Result::Err payload map, then choose field index zero and i64. The exact internal metadata branch taken in the observed binary was not decoded, so that attribution is not asserted.

The new Err registry records exact callable-link to provider-qualified record identity. It does not search unqualified function or record names. Existing immutable composite layout digests and owner counts admit only one exact provider physical layout. An Err-specific semantic snapshot additionally records ordered field names and provider-resolved type identities, including integer/text distinctions and qualified nested named types. It is compared before first-wins or overwrite metadata registration. Conflicting or unsupported semantic proof stays invalid and blocks only the new Err path; the common physical-layout policy is unchanged. A per-function MIR-value owner map carries that identity through fresh copies, Var/NamedVar bindings, assignments and conditional joins. Empty entries retain contradictory or invalidated proof; absent entries do not claim authority. Contradictory assignments remain conservatively invalid even after a later write, avoiding branch-order dependence.

Known Err extraction bypasses foreign HirType decoding. Classes keep pointer semantics. Structs require a matching current-table qualified declaration and use a typed pointer plus fresh Struct copy, retaining later struct value-copy behavior. Missing declaration/layout, contradictory proof, or a field absent from the exact known record is fatal; an integer placeholder after the fatal report is not successful admission. No Any/i64 coercion is introduced to hide an unknown type.

Ok, Some, custom enums and unmodeled legacy payload routes are unchanged. General indirect-call and unknown payload authority remains OPEN; this change does not establish a general foreign-SymbolId repair. Existing upstream Optional/conditional changes remain intact.

The semantic snapshot map persists with provider metadata and is promoted with transient roots; it is not cleared by per-function or thunk state changes. Its type walker terminates at qualified Named identity, recursively covers concrete containers/pointers, and refuses unsupported/inferred field types rather than inventing semantics. The value-owner map is initialized/reset with function state, saved/restored around trait thunks, and promoted with transient owner roots. The shared Err registry follows the existing bootstrap registry lifetime and promotion rules. Same exact callable with divergent provider owners remains an explicit conflict, never last-writer wins.

## Regression assets and pending admission

`test/01_unit/compiler/result_err_record_owner_spec.spl` lowers real parsed three-module HIR/MIR, asserts GetField index one plus text result type, provider call count one, direct/wildcard/aliased calls, scalar Err control, and equal/divergent conditional joins. Same-size i64/text duplicate-declaration and overwrite cases retain the original physical digest/count while requiring a semantic fatal diagnostic; an exact class-key control binds mir_class_identity to class_type_names and the canonical snapshot key. Additional actual field lowering supplies a wrong valid consumer Named ID while retaining the provider value authority. Writeback and metadata controls check assignment invalidation, absent versus conflicting proof, missing provider rejection and Ok/Err registry separation.

`test/fixtures/compiler/result_err_record_owner/{records,provider,main}.spl` is the native three-module positive: local IoError homonym has a different first-field type, provider message is the second field, aliases preserve it, a mutable Service call counter must stay exactly one, and mutation of a copied imported Struct Err payload must not alter the original. `conflicting_owner.spl` is a separate compile-negative entry, sharing the providers. It must report a fatal provider-layout conflict and produce no admitted executable.

No compiler, native fixture or compiled spec has run for this source change. Runtime source/producer/runtime/backend/cache pins, positive exact values and negative diagnostic/no-object proof are required before closure. Do not transfer a prior producer or a source-review PASS into native admission.
