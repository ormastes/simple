# Native codegen erases a trait-typed field receiver (`self.store.read`) to a bare ambiguous method

- **ID:** native_codegen_trait_field_receiver_erased_ambiguous_2026_10_26
- **Severity:** P1 (silent miscall class in seed) · **Status:** open (workaround active)
- **Producer:** fresh Rust seed (`C:/dev/seedlane/seed/simple.exe`) `native-build --entry-closure src/app/cli/main.spl`

## Failure
```
[CODEGEN-AMBIGUOUS-METHOD] in 'VirtualSourceConsumerAdapterV1.read' bare method 'read' has 14 candidates:
[File.read, FileHandle.read, FileTextSession.read, MirLoopConstructionViewV1.read, MirLoopSealedViewV1.read,
 Stdin.read, _InternalElfByteInputs.read, (+ _dot_ aliases)] — refusing to pick shortest
[CODEGEN-STUB-FALLBACK] body compilation failed for 'VirtualSourceConsumerAdapterV1.read'
```
This one site accounts for every AMBIGUOUS-METHOD and STUB-FALLBACK line in the full-CLI log
(6 ambiguous + 2 stub-fallback lines = 1 site, emitted in 3 forms x 2 passes).

## Root cause
`VirtualSourceConsumerAdapterV1.store` is declared `store: VirtualSourceStoreV1` (a trait), but for
`self.store.read(...)` the seed's method lookup (`codegen/instr/closures_structs.rs`, bare-method
candidate search) receives no type qualifier, so it searches every linked `*.read` by name suffix.
None of the 14 candidates implements the trait; any pick would miscall. Siblings `list`/`stat`/`page`
on the same receiver compile only because fewer same-name candidates exist (silent single-candidate
erased bind risk).

## Workaround
Bind the field to an explicitly typed local (`val store: VirtualSourceStoreV1 = self.store`) before
the call, in `src/compiler/00.common/cache_contract/virtual_source_consumer_v1.spl` (all four
methods). With the typed receiver the seed emits trait vtable dispatch (indirect `call *reg`
verified in the probe object), no ambiguity.

## Reproduce / prevention
Probe (seed, `SIMPLE_NATIVE_BUILD_RUST=1`): a class with field `store: Store` (trait) calling
`self.store.read(..)` while two other classes define `read` -> AMBIGUOUS-METHOD; the typed-local form
compiles (`compiled=1 failed=0`).

## Underlying fix (owner: seed codegen)
Propagate the declared field type of `self.<field>` into the method-call receiver type so a
trait-typed field receiver takes the trait-dispatch path. Remove the workaround after that fix is
verified with the full-CLI native-build.

**Revalidated 2026-11-02: still plausible because - Severity: P1 (silent miscall class in seed) · Status: open (workaround active); no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 lane s3g3: status, deferred with concrete blocker
- Source mitigations landed: `b6ec9253580` (typed-local receivers) and `a9994eb1e91` (null-object impl
  `UnavailableVirtualSourceStoreV1`, so every closure holding the trait also has a vtable).
- Seed already recovers field-chain receiver types (`recover_receiver_type`, `FieldAccess` arm in
  `mir/lower/lowering_expr.rs`) and has a runtime vtable-switch for ambiguous candidates
  (`try_emit_vtable_type_switch`, `closures_structs.rs`). The residual gap is a trait-typed field in a
  compilation unit that contains the trait but NO impl: there is no vtable to dispatch through and the
  trait name alone must not bind an arbitrary implementer (`qualified_method_owner_matches`). A real fix
  needs a seed codegen decision (emit fail-closed trait call vs. synthesize the vtable) plus a seed rebuild
  and a full-CLI native-build to confirm; not attempted without that loop. Workaround tags stay.
