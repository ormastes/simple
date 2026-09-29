# Iterator.collect generic restoration

Status: open

## Problem

`Iterator.collect` was declared as:

```simple
fn collect<C: FromIterator<Self.Item>>(self) -> C:
    return C.from_iter(self)
```

That source form is not native-compilable today. HIR drops method-level generic
parameters, so `C` is unavailable downstream, and native lowering cannot emit
the type-parameter static call `C.from_iter(self)`. Keeping the signature would
advertise a generic API that fails during native compilation.

The compile-safe compatibility ceiling is therefore array collection:

```simple
fn collect(self) -> [Self.Item]
```

It consumes the iterator and pushes each item into an array. This does not break
any working repository caller found in the 2026-07-17 audit: all iterator
`.collect()` call sites either infer an array or explicitly return/assign an
array. Calls to unrelated collector objects were excluded.

## Deferred surface

These existing `FromIterator` implementations cannot yet be selected through
`Iterator.collect`:

- `List<T>` in `src/compiler_rust/lib/std/src/core/list.spl`
- `FixedVec<T, N>` in `src/compiler_rust/lib/std/src/core_nogc/fixed_vec.spl`
- `StaticVec<T, N>` in `src/compiler_rust/lib/std/src/core_nogc_immut/static_vec.spl`

## Restoration condition

Restore the original generic signature only when all of the following hold:

1. HIR preserves method-level generic parameters and their bounds.
2. MIR/native lowering resolves and emits `C.from_iter(self)` for a type
   parameter constrained by `FromIterator<Self.Item>`.
3. Native tests cover array, `List<T>`, `FixedVec<T, N>`, and
   `StaticVec<T, N>` collection without special-case lowering.
4. The array-only `ponytail:` ceiling comment is removed with this bug.

Until then, callers needing a non-array collection must collect to an array and
construct the target collection explicitly.
