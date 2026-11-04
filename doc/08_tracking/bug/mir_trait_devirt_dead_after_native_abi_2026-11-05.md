# MIR trait-object devirtualization: unreachable for Named/dyn trait receivers after native ABI (2026-11-05)

## Decision (owner, 2026-11-05)
Keep the native trait-object ABI (vtable load + `CallIndirect` through
`lower_native_trait_method`) for trait-typed receivers. Do not keep devirtualization
as the path for them.

## Finding: nothing deleted, the fallback is still live
Since ac6c0a021c5 `lower_method_call` (`method_calls_literals.spl:~2340`) sends every
receiver whose type resolves via `native_trait_owner_for_type` (Named/DynTrait of a
Trait symbol) to `lower_native_trait_method`, so
`lower_trait_receiver_method_call` is unreachable for those. It is NOT dead overall:
`trait_receiver_identity` (`provider_metadata.spl:1017`) also admits `Trait?` payload
receivers (`Some(x)`, `if val`, `match Some`) and declared-field/param types that
`native_trait_owner_for_type` returns "" for (Optional wrapper). Those still reach the
legacy branch; `test/01_unit/compiler/mir/option_trait_payload_receiver_spec.spl`
(7/7 pass) pins that. The shared state (`trait_impl_owners`, `trait_impl_methods`,
`trait_impl_closure_complete`, `devirtualized_calls`) is also read by the scalar trait
path (`method_calls_literals.spl:5522`), the lifted-lambda copy
(`switch_operators_calls.spl:7984`) and the driver gate. Deleting any of it would
break existing behaviour, so no src change was made.

## Spec
`test/01_unit/compiler/50.mir/trait_typed_receiver_dispatch_spec.spl` rewritten to
assert the native ABI (CallIndirect, no direct `Mem.list`, no rt_panic, no errors for
0/1/N implementors and partial closure), a concrete receiver staying a direct call,
and the driver gate. Before: 1/11 pass. After: 9/9.

## Removed examples / follow-ups
- Stage3 bootstrap shape (`trait_impl_provider_modules`, no providers to
  `lower_module`): now fails with fatal `native trait dispatch lacks declaration:
  pkg.xm_a::Store` (native layouts are not registered from trait_impl_provider_modules).
  Verify whether any real driver lane takes that shape.
- Lifted lambda bodies with a trait-typed receiver (`\item: item.list(2)`) in a
  full-HIR lowering: fatal `native trait dispatch lacks declaration` because
  `switch_operators_calls.spl:~8093` copies `native_trait_layouts` into the lifted
  lowering only when `declaration_repository != nil`. Candidate fix: copy
  layouts/implementations/thunks unconditionally (needs its own spec + review).
- Re-add devirtualization of trait-typed receivers as a tested optimization pass only
  if perf measurement on a self-hosted binary justifies it.

## Update (review fixes)
- Lifted-lambda bug FIXED: `switch_operators_calls.spl` now copies
  `native_trait_layouts/implementations/thunks` into the lifted lowering and the thunks
  back unconditionally (previously only under `declaration_repository != nil`). Spec
  "lifted trait dispatch" is RED before, GREEN after (6 CallIndirect = 2 sites x 2 + 2
  from `callback(s)`).
- The stage3 "feed-only" example (`trait_impl_provider_modules` with no providers) was
  synthetic: the real driver passes `mir_feed_modules` as providers
  (`driver_pipeline_lowering.spl:1063,1078` -> `module_lowering.spl:2311`); the fallback
  at `provider_metadata.spl:916` only fires with empty providers. Dropped, with the
  spec helper param removed. The earlier follow-up bullet on it is superseded.
- Each trait-typed call site emits 2 CallIndirect (slot call + copy thunk,
  `native_trait_conversion.spl:349`); specs assert exact counts. Generic implementor
  example re-added (native ABI: 0 errors).
