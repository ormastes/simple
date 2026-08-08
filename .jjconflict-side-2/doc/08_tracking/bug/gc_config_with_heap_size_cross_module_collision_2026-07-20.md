# `GcConfig.with_heap_size` unresolvable — one specific static method missing from an otherwise-working class, identical struct/impl defined in 3 sibling family modules

**Date:** 2026-07-20
**Component:** interpreter class/impl registry — `struct GcConfig` +
`impl GcConfig` defined identically in `src/lib/nogc_sync_mut/gc.spl`,
`src/lib/nogc_async_mut/gc.spl`, and `src/lib/gc_async_mut/gc.spl`.
**Severity:** Medium — `GcConfig.with_heap_size` is unreachable via any
family's import path even though the method is textually present in the
imported file; other static methods on the same class (`default()`) and on
sibling classes in the same file (`GcStats.new()`) resolve fine.

## Symptom

`test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl`, example
`"uses nogc_sync_mut for sync GC metadata"`, fails under `bin/simple test`:

```
NoGC sync mutable runtime contracts
  when configuring GC-adjacent hosted services
    ✗ uses nogc_sync_mut for sync GC metadata
      semantic: unknown static method with_heap_size on class GcConfig
  when using pointer handles
    ✓ uses nogc_sync_mut pointer helpers as the sync backend
```

## Minimal repro

Run **from inside the repo root** (module resolution needs the project
`std.*` root — a repro run from an unrelated cwd/scratch dir gives a
misleading "module path segment `std` not found" instead of this error):

```simple
use std.nogc_sync_mut.gc.{GcConfig, GcStats}
fn main():
    val d = GcConfig.default()
    print("default ok young={d.young_size}")          # prints fine
    val s = GcStats.new()
    print("GcStats.new ok collections={s.collections}") # prints fine
    val c = GcConfig.with_heap_size(20 * 1024)         # fails
    print("with_heap_size ok young={c.young_size}")
main()
```

Run: `bin/simple run <this file>` on the deployed binary
`bin/release/x86_64-unknown-linux-gnu/simple` from `/home/ormastes/dev/pub/simple`
— **fails the same way even under `run`** (confirmed in-tree, not a
cwd/resolution artifact):

```
default ok young=1048576
GcStats.new ok collections=0
error: semantic: unknown static method with_heap_size on class GcConfig
```

Also confirmed independent of argument type coercion: passing an explicit
`val sz: usize = 20480; GcConfig.with_heap_size(sz)` fails identically.

This rules out the known "static method unresolved under `test` only"
landmine (`generic_class_static_method_unresolved_under_test_2026-07-20.md`)
— this one is a plain runtime/semantic failure under `run` too, and it is
specific to this one method, not "the whole class"/"the whole impl block".

## Root-cause hypothesis

`with_heap_size` is NOT missing from source — it's defined identically (same
line number, 139) in all three sibling copies of `struct GcConfig` /
`impl GcConfig`:

```
$ grep -n 'static fn with_heap_size' src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/gc.spl
src/lib/nogc_sync_mut/gc.spl:139:    static fn with_heap_size(size: usize) -> GcConfig:
src/lib/nogc_async_mut/gc.spl:139:    static fn with_heap_size(size: usize) -> GcConfig:
src/lib/gc_async_mut/gc.spl:139:    static fn with_heap_size(size: usize) -> GcConfig:
```

Given `GcConfig.default()` (same impl block, works) and `GcStats.new()`
(different class, same file, works) both resolve fine while
`GcConfig.with_heap_size` alone fails, this is NOT a "whole impl block lost
to a sibling collision" — the impl block that IS registered for `GcConfig`
is clearly reachable and mostly correct. The likely mechanism (unconfirmed,
not traced into Rust source) is that with three files defining an identical
`struct GcConfig` name, the class/method registry key is
`(class_name, method_name)` and something about `with_heap_size`
specifically — it's the only multi-statement static constructor in the
group that mutates a `var config` (`var config = GcConfig.default(); config.
young_size = size / 5; ...; config`) rather than a single struct-literal
return like `default()` — causes it to be dropped or overwritten by one of
the sibling copies during registration while the simpler statics survive.
Not traced further into the Rust interpreter's global type/method registry
(`interpreter_extern`/`hir` class table) — that's the next step for whoever
picks this up.

## Notes

- Do NOT attempt a Rust seed source fix here (out of scope for this triage
  pass; needs a rebuild to verify).
- Spec left RED, assertion NOT weakened.
- Affected: `test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl`
  (1 of 2 examples fails; the pointer-handle example in the same file
  passes cleanly).
