# Bug: Native Any Parameter Forwarding Corrupts Pointer

Status: RESOLVED 2026-08-24 (see the 2026-08-24 section at the end — the fixture-level divergence was a DIFFERENT defect: Any-to-text interpolation in native codegen).
Status re-verified 2026-08-17 by source inspection (triage shard 02).
default-LLVM + explicit-Cranelift forwarding proof added, execution pending.

**Date:** 2026-06-05
**Severity:** High
**Component:** compiler/codegen (Cranelift native)
**Status:** Pure-Simple one-word ABI source fixed; strict default-LLVM + explicit-Cranelift
wrapper-to-extern regression added to `scripts/check/check-native-seed-parity.shs`;
execution awaits a fresh pure-Simple compiler binary.

## Description

When a closure is passed through a Simple function parameter typed as `Any`,
then forwarded to an extern fn also taking `Any`, the closure pointer arrives
at the C function as a non-canonical >48-bit address, causing a segfault.

Direct extern call (no wrapper function) passes the correct pointer.

## Reproduction

```simple
extern fn rt_thread_spawn_isolated(closure: Any) -> i64

fn worker() -> i64:
    return 42

# WORKS — direct extern call from main
fn main_ok():
    val h = rt_thread_spawn_isolated(\: worker())  # arg0 = valid heap ptr

# CRASHES — forwarded through Any parameter
fn my_spawn(closure: Any) -> i64:
    return rt_thread_spawn_isolated(closure)  # arg0 = >48-bit non-canonical

fn main_fail():
    val h = my_spawn(\: worker())  # segfault
```

## Root Cause (hypothesis)

The native codegen double-encodes or corrupts the 2-slot Any representation
(type_tag: i64, value: i64) when loading it from a function parameter's local
storage and re-passing it to another call. The widening from a concrete type
to Any at a call site works correctly.

## Workaround

Changed `thread_spawn(closure: Any)` to `thread_spawn(closure: () -> i64)`.
The concrete closure type passes as a single i64, widened to Any only at the
extern call site — which is the path that works.

2026-06-22 hardening: `src/lib/nogc_sync_mut/concurrent/thread.spl` now matches
the std concurrency surface by declaring `rt_thread_spawn_isolated` externs with
`closure_ptr: i64` and casting closures at the direct extern call site. The
`thread_spawn_with_args` wrapper also takes `fn(Any, Any) -> Any` instead of
forwarding a closure through a wrapper parameter typed `Any`.

Regression guard:
`test/01_unit/lib/nogc_sync_mut/concurrent_thread_pointer_spawn_spec.spl`.

## Related

- `rt_thread_join -> Any` return also broken: C returns 1 I64 but `-> Any`
  expects 2 I64 slots. Fixed by declaring `-> i64` instead.
- Native `List<T>` indexing with loop variables also produces wrong results
  (separate bug).

---

## 2026-08-24 — REOPENED, root-caused, RESOLVED (a different defect under the same fixture)

The engine-differential gate's `any_vs_typed_list_param` fixture diverged on the
NATIVE lane only (interpret and jit agreed). Measured on origin/main
`6119ba3878f`, seed
`a1387e23c4f015aa9a09f373f32f24c60383647b944b48558eb5eab1df100241`:

```
interpret/jit: typed_sum=100 typed_first=10 any_of_elem=10 any_of_int=30  any_of_bool=true any_of_text=hi
native (before): typed_sum=100 typed_first=10 any_of_elem=80 any_of_int=240 any_of_bool=11 any_of_text=<pointer>
native (after):  typed_sum=100 typed_first=10 any_of_elem=10 any_of_int=30  any_of_bool=true any_of_text=hi
```

**Not parameter forwarding.** A minimal probe with no `Any` parameter at all
(`val a: Any = 30; print("{a}")`) reproduced it identically, which kills the
2026-06-05 forwarding hypothesis. `typed_sum` was already correct on current
origin/main (fixed separately by `8eadd36a2d6`); the task's reported
`typed_sum=0` predates that landing.

**Root cause.** `HirTypeKind.Any` lowers to `MirTypeKind.I64` — the *tagged*
any slot (`src/compiler/50.mir/_MirLowering/function_lowering.spl`, `Any` arm).
`coerce_concat_operand`
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`), the shared
interpolation/concat render dispatch, keys ONLY off the MIR type, so an `Any`
local matched `is_numeric` and was rendered with `rt_raw_i64_to_string` — the
raw tagged word, never untagged. The observed values are exactly that:
`30 -> 240` (`30<<3`), `10 -> 80`, `true -> 11` (`(1<<3)|3`), text -> its
pointer. This is the same defect class as the `Some(<float>)` payload bugs
(`4cc714ece3e`, `51a7b28e220`): a value crossing an erased boundary being
handled by its erased representation instead of its real one.

**Fix (minimal).** In `coerce_concat_operand`, before the MIR-type scalar
dispatch, consult the already-recorded declared HIR type via
`find_local_hir_type`; when it is `HirTypeKind.Any`, emit a call to
`rt_value_to_string` (tagged in, tagged out) — the same runtime entry the
`str(x)` builtin already uses for any-typed values — and mark the result a
tagged text local. Pure-Simple compiler side; no Rust-seed change.

Status: RESOLVED — commit `eaac3400b86`.

### Gate state after the fix (clean worktree at `6119ba3878f`, seed sha256 `a1387e23…`)

```
[any_vs_typed_list_param] AGREE
divergences:       2 (2 NEW, unbaselined)
FAIL — 2 unbaselined divergence(s) among 13 fixture(s) compared
FAIL — 13 fixture(s) checked, unbaselined divergence(s)=1
```

The gate is still FAIL, on two **pre-existing** fixtures this change did not
touch: `i64_boundary_values` (`shl64`/`shl65`/`shr64` render as pointer-magnitude
integers on native) and `f64_roundtrip` (`list_sum`/`boxed0` denormal garbage).
Both were reproduced byte-for-byte on an UNPATCHED worktree of the same commit
with the same seed, so this range fixes one divergence and introduces zero.
Both belong to the filed
`int61_bit_truncation_jit_scalars_and_native_container_boxing_2026-08-09.md`
class and are deliberately left unbaselined by the harness. They were NOT
baselined to force green.

Also observed and unchanged: the wrapper's `unbaselined divergence(s)=1` is a
status, not a count — the harness's own `divergences:` line is authoritative
(`check-engine-differential.shs:51` prints the harness rc). Not fixed here;
belongs to the engine-differential lane.
