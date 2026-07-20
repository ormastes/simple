# `PersistentVec.from_array` / `.of` unresolved as static methods (works for `.empty`/`.range`/`.repeat`)

**Date:** 2026-07-20
**Found by:** whole-suite `test/unit/` triage campaign, cluster
`test/unit/lib/{gc_async_immut,gc_sync_immut}`
**Status:** open — genuine defect, reproduces under both `bin/simple run`
and `bin/simple test` (NOT the known test-vs-run static-method landmine)

## Symptom

```
semantic: unknown static method from_array on class PersistentVec; did you mean 'to_array'?
```

```
semantic: unknown static method of on class PersistentVec
```

Both `PersistentVec.from_array(arr)` and `PersistentVec.of(arr)` fail to
resolve, even though both are `static fn` members defined directly in the
class body at `src/lib/nogc_async_immut/persistent_vec/__init__.spl:406-415`:

```simple
static fn of(arr: []) -> PersistentVec:
    return PersistentVec.from_array(arr)

static fn from_array(arr: []) -> PersistentVec:
    var result = PersistentVec.empty()
    var i = 0
    val n = arr.len()
    while i < n:
        result = result.push(arr[i])
        i = i + 1
    return result

static fn empty() -> PersistentVec:
    return PersistentVec(root: nil, tail: [], size: 0, shift: 0)
```

`PersistentVec.empty()`, `.range(start, end)`, and `.repeat(value, n)` (also
static methods on the same class) resolve and work correctly. Only `.of` and
`.from_array` — both of which take a single array-typed parameter (`arr: []`)
— fail.

This reproduces under **`bin/simple run`**, not just `bin/simple test`:

```simple
use std.gc_async_immut.{PersistentVec}

fn main():
    val sample = PersistentVec.from_array([4, 5, 6])   # BUG: unknown static method
    print(sample.len())
```

A minimal isolated repro with a toy class (`static fn make(arr: []) -> Foo`
alongside `static fn zero() -> Foo`) does NOT reproduce — both resolve fine —
so the defect is specific to something about `PersistentVec`'s actual
declaration (possibly method count, declaration order, or an interaction
with the `of` method's body calling `PersistentVec.from_array` internally)
rather than the `arr: []` parameter shape in general.

## Affected specs

- `test/unit/lib/gc_async_immut/persistent_vec_native_spec.spl` — `PersistentVec.from_array([4, 5, 6])`
- `test/unit/lib/gc_sync_immut/persistent_vec_native_spec.spl` — identical, same line

Both specs are otherwise correct against the current API — `PersistentVec`
is the documented canonical constructor (`src/lib/nogc_async_immut/persistent_vec/transient.spl`
comments explicitly instruct callers to use `PersistentVec.from_array(...)`)
and there is no alternate value-preserving spelling available from the class
itself (the only workaround is a manual push-loop, which would test a
different code path than the spec intends — NOT a value-preserving rewrite,
so left unmodified per the "never weaken/rewrite to force green" rule).

Note: `src/lib/nogc_async_mut/__init__.spl` separately exports free-function
aliases `PersistentVec__empty`, `PersistentVec__from_array`, `PersistentVec__of`,
`PersistentVec__repeat`, `PersistentVec__range` alongside the class — these
appear to be a pre-existing workaround pattern for static-method dispatch
issues on this exact class, which is circumstantial evidence this static
method resolution gap is already known at the library-author level, just not
previously bug-tracked or spec-migrated.

## Second confirmed instance: `GcConfig.with_heap_size` (same defect class, different subsystem)

`test/unit/lib/nogc_sync_mut/gc_runtime_contract_spec.spl` hits the identical
symptom shape on an unrelated class:

```
semantic: unknown static method with_heap_size on class GcConfig
```

`src/lib/nogc_sync_mut/gc.spl:139` defines `static fn with_heap_size(size:
usize) -> GcConfig` inside `impl GcConfig:` (a `struct`, not `class` — so
this is NOT the enum-only `impl`-block landmine in
`enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20.md`,
which explicitly found `class`/struct-style `impl` blocks unaffected).
Reproduces under `run`:

```simple
use std.nogc_sync_mut.gc.{GcConfig}
fn main():
    print(GcConfig.default().young_size)        # 1048576 -- works
    print(GcConfig.with_heap_size(1024))         # unknown static method -- BUG
```

`GcConfig.default()` (the first static method in the same `impl` block)
resolves fine; `GcConfig.with_heap_size()` (the second, and the only other
static method in the block) does not. As with `PersistentVec`, this rules
out a simple "first N statics only" or "last static only" positional theory
— `default` (1st) works, `with_heap_size` (2nd, and only one other) fails;
for `PersistentVec`, `range`/`repeat` (1st/2nd) and `empty` (5th/last) work
while `of`/`from_array` (3rd/4th) fail. Both failing methods' bodies call
another static method of the *same* class internally (`with_heap_size` calls
`GcConfig.default()`; `from_array` calls `PersistentVec.empty()`) — but so do
the passing ones (`range`/`repeat` also call `PersistentVec.empty()`
internally), so self-referential static calls are not the differentiator
either. Root cause not isolated further this pass.

## Scope note

No Rust seed source fix attempted (out of scope for this triage pass per the
fix-guide; needs a rebuild). Left as GENUINE-BUG, both specs unmodified.
