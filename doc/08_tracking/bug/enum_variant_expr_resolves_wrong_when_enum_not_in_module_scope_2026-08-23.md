# `EnumName.Variant` in expression position resolves wrongly when the enum is not in the module's import scope

- **Filed:** 2026-08-23
- **Status:** OPEN (compiler). The two specs it broke are fixed at the library
  level; the interpreter defect below is untouched and still reachable.
- **Engine:** Rust seed **interpreter**. `bin/simple run` on the same source got
  the right answer via a lenient dynamic fallback, so this is only visible on
  the spec/test path — which is exactly why it hid.

## Symptom

`test/03_system/feature/scilib/ndarray_sort_spec.spl` and
`ndarray_concat_stack_spec.spl`, verbatim pre-fix:

```
NDArray sort
  ✗ returns UnsupportedDType for Bool argsort
    expected false to equal true
Results: 5 total, 4 passed, 1 failed

NDArray stack
  ✗ returns UnsupportedDType for Bool stack in this 1-D v1 slice
    expected false to equal true
Results: 6 total, 5 passed, 1 failed
```

Both guards exist and look correct
(`ndarray_impl_ops.spl:187`, `ndarray_generators.spl:171`):
`if arr.dtype == DType.Bool: return Err(NdarrayError.UnsupportedDType)`.

## Measured evidence

A probe compiled inside `ndarray_impl_ops.spl` (the module that owns the broken
guard) returned, for an array whose dtype genuinely is `DType.Bool`:

| expression | value |
|---|---|
| `match arr.dtype: case DType.Bool` | **true** |
| `match DType.Bool: case DType.Bool` | **false** |
| `arr.dtype == DType.Bool` | **false** |
| `DType.Bool == DType.Bool` | true |
| `arr.dtype == arr.dtype` | true |

Row 2 is the whole story: the **expression** `DType.Bool`, evaluated in that
module, is not `DType::Bool` — it is some other self-consistent value, which is
why row 4 is true and rows 2 and 3 are false. The same expression evaluated in
a module that does `use std.ndarray.*` is correct.

`arr.dtype is DType.Bool` fails identically, so the
`EnumVariantConstructor` bridge that `BinOp::Is` has
(`interpreter/expr/ops.rs:1213-1229`) does not rescue it — and `BinOp::Eq` /
`BinOp::NotEq` (`ops.rs:1007`, `:1037`) have no such bridge at all.

## Root cause

`ndarray_impl_ops.spl` and `ndarray_generators.spl` reference `DType` and
`NDArray` without importing `std.ndarray.mod` — they cannot, because `mod.spl`
imports *them* (circular). The interpreter therefore resolves the bare name
`DType` through a **flat global enum/class table**
(`interpreter/expr/calls.rs:770-795`), and there are **three** distinct enums
named `DType` in the tree:

- `src/lib/nogc_async_mut/ndarray/mod.spl` (F32 F64 I64 Bool) — the intended one
- `src/lib/nogc_sync_mut/src/tensor.spl:36` (F16 F32 F64 I8 I16 I32 I64 U8 Bool …)
- `src/lib/nogc_sync_mut/src/dl/config.spl:10` (F16 F32 F64 BF16 I8 …)

The lookup is by bare name with no module scoping, so it can pick the wrong
`DType` — silently, producing a value that compares unequal to the correct one
rather than raising. This is the same silent-wrong-resolution class as
`doc/08_tracking/bug/interpreter_cross_module_enum_discriminant_3_compares_false_2026-08-04.md`
(which fixed the in-scope case, where `DType.Bool` picked up the std struct
`Bool`'s constructor) — that fix does not cover the not-in-scope case here.

## Verdict: genuine defect, NOT unimplemented

Explicitly checked against the `@tag:in-development` bar
(`src/lib/nogc_sync_mut/spec/in_development.spl`): **it does not qualify.** The
`Bool`-rejection guards are fully implemented and present in source at both
sites; they simply never fire. The docstring hints about "1-D v1 slice" describe
scope of the ndarray feature, not a missing guard. The specs assert real,
implemented behaviour and were correct to be red.

## Library-level fix applied (this change)

`enum DType` moved from `src/lib/nogc_async_mut/ndarray/mod.spl` to
`src/lib/common/science_math/ndarray.spl` as `pub enum DType`, with variants
and order unchanged. That file is already documented as the home of the NDArray
core types and is already imported by `mod.spl`, `ndarray_generators.spl`,
`ndarray_impl_ops.spl` and `ndarray_simd.spl` — so `DType` becomes explicitly
in scope everywhere it is used, and the ambiguous global lookup is never
reached. Zero semantic change: same variants, same order, same public surface
via `std.ndarray.*`.

## Still open (compiler)

The interpreter should not silently resolve a bare `EnumName` to an
arbitrary same-named enum from another module. Two candidate fixes, neither
attempted here because both are larger than this change's scope:

1. Module-scope the enum lookup at `interpreter/expr/calls.rs:770`, and error
   loudly (rather than guess) when the name is ambiguous or not in scope.
2. As a strictly weaker mitigation, give `BinOp::Eq`/`NotEq`
   (`ops.rs:1007`, `:1037`) the discriminant bridge `BinOp::Is` already has at
   `ops.rs:1213`. This would not fix the wrong-enum case and must not be
   mistaken for a fix.

Any repo carrying duplicate enum names across modules is exposed. A census of
duplicate top-level enum names would size the blast radius.

## Tests

- `test/01_unit/lib/nogc_async_mut/ndarray_bool_dtype_guard_spec.spl`
  (+ mirror in `test/unit/`) — reproduce plus neighbouring guards in the class.
- `test/03_system/feature/scilib/ndarray_sort_spec.spl`,
  `ndarray_concat_stack_spec.spl` — the filed specs, now green.
