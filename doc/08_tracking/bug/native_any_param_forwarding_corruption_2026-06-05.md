# Bug: Native Any Parameter Forwarding Corrupts Pointer

Status: One-word Any ABI supersedes the reported two-slot premise; strict
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
