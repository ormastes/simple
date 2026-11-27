# Mono leaves generic<T>(local.field) unspecialized when local = opt.unwrap()

Status: FIXED in source (unverified by a rebuilt compiler; see Verification)

Symptom: Stage 2 Phase 3 fails with `E-MONO-033` / `E-MONO-032: call to generic
transient_promote at reverse_reference_facts.spl` for calls like
`transient_promote(batch.facts)` where `val batch = G.unwrap()`.

Repro: `build/repro/field_arg.spl` (class + `Batch?` global, `val batch =
_g.unwrap()`, `promote(batch.facts)`). Compiled with the Stage 2 producer
`compile --format=smf`: `[mono] ... unresolved=2`, E-MONO-032 "argument inference
has no concrete local type". Variants `val batch: Batch = _g.unwrap()` and
`val batch = Batch(...)` both give `unresolved=0`, so field access itself is fine.

Root cause: `MonomorphizationPass.infer_expr_type_invocation_inner_v1`
(src/compiler/40.mono/monomorphize_integration.spl, MethodCall case) answered
nil for every method that is not a generic-impl method, including the builtin
`Optional.unwrap()`. The unannotated local therefore got no env type, and
`infer_field_chain` could not type `batch.facts`.

Fix: the MethodCall case returns `optional_payload_type(infer_expr_type(recv))`
for a zero-arg `unwrap` that is not a generic-impl method.

Regression spec: test/01_unit/compiler/mono/mono_field_access_arg_after_unwrap_spec.spl
(authored, not executed).

Verification: a source change in 40.mono needs a rebuilt compiler; the prebuilt
Stage 2 cannot confirm it. Removal check for the typed-local workaround in
reverse_reference_facts.spl (tag `@workaround bug=mono_generic_field_access_arg_unspecialized_2026-10-23`):
restore the original `transient_promote(batch.facts)` form after a Stage 2 built
from this fix, then rebuild Phase 3.
