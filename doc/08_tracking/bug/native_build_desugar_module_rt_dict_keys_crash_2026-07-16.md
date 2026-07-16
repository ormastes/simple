---
id: native_build_desugar_module_rt_dict_keys_crash_2026-07-16
status: FIXED
severity: high
discovered: 2026-07-16
discovered_by: lane r_cranelift_statics, chasing a 3-lane report of cranelift
  "Failed to declare module statics" at tip 45dcd340f16
related: src/compiler/10.frontend/desugar/desugar_async.spl
related: src/compiler/70.backend/backend/cranelift_codegen_adapter.spl
related: doc/08_tracking/bug/cranelift_seed_missing_sffi_externs_2026-07-16.md
---

# native-build was broken for EVERY backend (llvm AND cranelift) at desugar_module, not just cranelift statics

## Summary

This lane was dispatched to root-cause cranelift's
`"Failed to declare module statics"` error. That specific error text is
**not** reachable at current tip: it was already fixed earlier (see
`cranelift_seed_missing_sffi_externs_2026-07-16.md` § "Related latent fix
banked in the adapter" — `declare_module_statics` now returns a plain
`Dict<i64,i64>` with a `-1` sentinel instead of an `Option<Dict>` that the
interpreter erased to nil).

What **is** reproducible at tip `45dcd340f16` is a strictly earlier,
backend-agnostic crash that fails `native-build` for every case on every
backend before codegen is ever reached — including a bare
`fn main(): print(42)`:

```
error: semantic: type mismatch: cannot convert dict to int
```

Confirmed with `scripts/check/native-smoke-matrix.shs`: **total=15 pass=0
fail=15**, identical error tail on every single case, for both `--backend
llvm` and `--backend cranelift`. `bin/simple run` (interpret-only, no
native-build) on the same file works fine, isolating the bug to the
native-build frontend pipeline.

## Root cause

`src/compiler/10.frontend/desugar/desugar_async.spl` `desugar_module()`
called the raw SFFI extern `rt_dict_keys(module.functions)` (imported via
`use std.alloc.sffi.{rt_dict_keys}`) directly on a live interpreter `Dict`
value, instead of using the `.keys()` method that every other call site in
`src/compiler/` uses (see `module_lowering.spl`, `declaration_lowering.spl`,
`generalization.spl`, `trait_impl_lowering.spl`, etc.). This is exactly the
documented seed-compat landmine: `rt_dict_*`/`rt_tuple_*` externs are for
codegen-emitted calls in AOT-compiled target programs (see
`llvm_lib_translate.spl:414` declaring `rt_dict_keys` for that purpose), not
for the deployed seed's own live interpretation of compiler source. Called
directly during self-interpretation, the extern receives/returns a shape the
interpreter's `Value::as_int()` coercion can't handle, surfacing as a
generic, location-less `"type mismatch: cannot convert dict to int"`
diagnostic — which is why it looked cryptic and was easy to conflate with
the (already-fixed) cranelift statics error.

Confirmed by trace bisection (`SIMPLE_COMPILER_TRACE=1` plus temporary
`print()` probes): the crash occurs precisely at
`rt_dict_keys(module.functions)`, immediately after entering
`desugar_module`, before any per-function work happens — so it fires
identically regardless of program content or target backend.

Two more call sites in the same function had the identical pattern:
`rt_dict_keys(generated_helper_functions)` and
`rt_dict_keys(module.actors)`.

## Fix

In `src/compiler/10.frontend/desugar/desugar_async.spl`:
- `module.functions.keys()` instead of `rt_dict_keys(module.functions)`
- `generated_helper_functions.keys()` instead of
  `rt_dict_keys(generated_helper_functions)`
- `module.actors.keys()` instead of `rt_dict_keys(module.actors)`
- Dropped the now-unused `use std.alloc.sffi.{rt_dict_keys}` import.

No rebuild needed (`src/compiler` is interpreted live by the deployed seed).

## Verification

- `sh scripts/check/native-smoke-matrix.shs`: **total=15 pass=15 fail=0
  codegen_fallback_hits=0** (was 0/15 before the fix).
- `fn main(): print(42)` via `native-build --backend=llvm`: builds and runs,
  prints `42`.
- `fn main(): print(42)` via `native-build --backend=cranelift`: now
  progresses past the desugar/frontend stage and past
  `declare_module_statics` (the "[cranelift-direct] start/target" trace
  prints appear), and fails only with the already-tracked, XFAIL-gated
  missing-SFFI-extern error:
  `error: semantic: unknown extern function: rt_cranelift_new_aot_module_triple`
  — this is the separate, pre-existing gap tracked in
  `cranelift_seed_missing_sffi_externs_2026-07-16.md` (deployed seed predates
  the full `rt_cranelift_*` surface); the parity harness's
  `cranelift_seed_supported()` probe correctly downgrades this to XFAIL, not
  a loud FAIL.
- `scripts/check/check-native-seed-parity.shs` with
  `NATIVE_PARITY_CASES="bare_main crossmodule_field_index_collision
  local_lambda_value"`: both `_llvm` legs of `bare_main` and
  `crossmodule_field_index_collision` now PASS (previously would have failed
  at desugar_module for every case); all three `_cranelift` legs correctly
  XFAIL on the missing-extern signature.

## Not fixed (out of scope, found incidentally)

`local_lambda_value_llvm` in the parity harness still fails — but on an
unrelated, pre-existing error: `error: HIR lowering error ...: unresolved
type: fn`. This is a distinct local-lambda/closure HIR lowering bug, not a
native-build-wide blocker and not related to module statics or dict
handling. Left as-is; worth a separate bug doc/lane if not already tracked.

## Patch

`scratchpad/r_cl_statics.patch` in the main repo (single file:
`src/compiler/10.frontend/desugar/desugar_async.spl`).
