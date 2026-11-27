# LLVM suffix-match fallback binds an untyped receiver to any same-name user method (2026-11-08)

**Status:** fix-implemented-verification-pending, P1 (see Fix 2026-11-13). Root hazard behind `stage2_new3_native_build_worker_av_c01_2026-11-07`.

## Problem
When MIR leaves a name-dispatched method call whose receiver type is ANY (owner unknown), the LLVM
codegen fallback resolves it by leaf name + arity across the whole link closure. If exactly one user
method matches (e.g. `StrictSdnReaderV1.byte_at(offset)`), the call is bound to it directly, even
though the receiver may be a text, array or unrelated object. The callee then reads the receiver as
its own class layout and access-violates (c01: read at 0x48).

## Why the c01 fix is not enough
#7857 makes `text?.unwrap()` typed STRING, closing that one source of ANY receivers. Any other path that
yields an ANY receiver plus a colliding leaf name still silently miscompiles into a wrong direct call.

## Expected
A name-dispatched call on an ANY receiver must use runtime dispatch (or fail the build loudly), never
a static bind chosen only by leaf + arity. Suggested gate: bind statically only when the receiver's
static owner is known and matches.

## Repro
Single file: a class with `fn byte_at(offset: i64)` and a function whose receiver is ANY
(e.g. via an untyped unwrap on a pre-fix seed) calling `.byte_at(i)`; `native-build --backend llvm`
emits a direct call to the class method (SEGV / 0xC0000005).

## Fix (2026-11-13)
- **Status:** fix-implemented-verification-pending (seed redeploy + native c01 re-run pending).
- Fix on `origin/release/1.0.0`: `9a6f40b38dc` (PR #7873,
  `src/compiler_rust/compiler/src/codegen/llvm/functions.rs` MethodCallStatic suffix fallback):
  a bare leaf on an ANY/UNKNOWN receiver clears the sole suffix candidate and falls through to the
  bare extern, which links only if a real symbol exists. Owner-qualified names still bind.
  Follow-up `12e9a9b35ce` maps the bare `byte_len` leaf that this exposed to `rt_string_len`.
- Regression: Rust unit tests in `functions.rs` `mod tests`
  (`erased_receiver_bare_leaf_is_not_bound_to_sole_user_method`,
  `primitive_receiver_bare_leaf_is_not_bound_to_user_method`,
  `owner_qualified_name_still_binds_the_user_method`); not run here (no cargo on this host lane).
- The pure-Simple LLVM backend (`_MirToLlvm/core_codegen.spl`
  `bootstrap_llvm_function_index_for_name`) already resolves exact name -> module-local bare name
  only and has no cross-closure leaf guess.
- Residual hazard for the owner (not changed): the `MirInst::Call` suffix scan in
  `codegen/llvm/functions/calls.rs` (~line 2690) still accepts the shortest same-leaf, same-arity
  `Owner.<leaf>` when the first argument is ANY/UNKNOWN (only primitive receivers are owner-checked),
  and `functions.rs` does not owner-check a sole candidate against a known non-primitive class
  receiver. Making those fail closed needs a seed build and native-lane run to prove no lane relies
  on the guess.
