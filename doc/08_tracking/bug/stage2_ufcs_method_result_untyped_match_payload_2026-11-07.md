# Stage2: UFCS method result leaves match scrutinee untyped

- **ID:** stage2_ufcs_method_result_untyped_match_payload_2026-11-07 — status open.

## Re-check 2026-11-08 (lane bootp2)
The run13 failing site no longer exists: commit `74d077aafda` ("align trait impls and stale
method callers with Stage 2 MIR") rewrote `src/compiler/99.loader/loader/module_loader.spl:747`
to the direct call `objtaker_take_with_types(moduleloader_ensure_obj_taker(self), ...)`, so the
stage3 closure no longer contains the UFCS shape. The compiler root (a UFCS-alias method's
declared return type not propagated to a `match` subject in 50.mir) was not reproduced or fixed
here; it belongs to the unresolved-method-call cluster. Re-confirm with an in-process HIR+MIR
probe of `x.take_with_types(...)` matched by `case Code(..)` before closing.

## Fix 2026-11-08 — fix-implemented-verification-pending
Self-hosted root (same hazard class as the seed LLVM suffix-match fallback,
`llvm_suffix_match_fallback_binds_untyped_receiver_to_user_method_2026-11-08`):
`TypeChecker.is_compatible` treats `Infer` as compatible with anything, so
`MethodResolver.try_ufcs` bound a method call on an untyped receiver to any
same-name free function with a concrete first parameter, and the call result
then carried that unrelated function's return type into `match`.
`try_ufcs` now consults `ufcs_receiver_may_bind_param`
(`src/compiler/35.semantics/resolve_strategies.spl`): an `Infer` receiver may
only bind a `TypeParam`/`Infer` first parameter; otherwise resolution stays
Unresolved and MIR's typed paths / loud `unresolved method call` rt_panic decide.
Self-hosted MIR (`reject_unresolved_method_call_v1`) and the Cranelift adapter
have no leaf-name suffix fallback (checked); the seed's
`src/compiler_rust/compiler/src/codegen/llvm` suffix match is NOT fixed here
(seed owner).
Evidence: `test/01_unit/compiler/semantics/ufcs_untyped_receiver_fail_closed_spec.spl`
5/5 FAIL before (function absent), 5/5 PASS after. Neighbor
`resolve_methods_quiet_typed_spec.spl` is 1/4 both before and after (pre-existing).
Native verification (stage2 rebuild) pending.
