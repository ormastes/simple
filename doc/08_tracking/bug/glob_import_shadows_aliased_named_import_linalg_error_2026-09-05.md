# A glob `use std.X.*` shadows an explicit aliased named import of the same type name

- **Filed-on:** 2026-09-05
- **Area:** compiler / module name resolution (Rust seed)
- **Priority:** P1
- **Status:** open
- **Blocks:** REQ-SCILIB-LAPACK-08 in
  `test/03_system/plan_acceptance/scilib_port_lapack_spec.spl`

## Symptom

Two distinct enums are both named `LinalgError`:

| enum | file | `Singular` shape |
|------|------|------------------|
| Layer B LAPACK | `src/lib/common/science_math/lapack.spl:38` | `Singular(row: i64)` |
| Layer C linalg | `src/lib/nogc_async_mut/linalg/linalg_core.spl` (re-exported by `std.linalg`) | `Singular` (no payload) |

A module that imports the first **explicitly and under an alias** and the
second **via a glob** gets the glob's binding for the alias:

```
use std.common.science_math.lapack.{LinalgError as LapackError, MockLapackProvider}
use std.linalg.*                       # also exports a `LinalgError`

match provider.gesv(2, [1.0, 1.0, 2.0, 2.0], [1.0, 2.0]):
    case Err(LapackError.Singular(row: r)):  # NEVER TAKEN
        ...
    case Err(_):                             # taken instead
        ...
```

Measured: `is_err()` is `true` and the value really is
`lapack.LinalgError.Singular(row: 1)` — with the `use std.linalg.*` line
**removed** the `row:`-bearing arm matches and prints `row=1`. Adding the glob
back makes the same arm dead.

## Why this is a defect and not a naming accident

An explicit named import is the most specific binding a module can state, and
an alias is an unambiguous rename. A glob is the least specific. Resolution
that lets the glob win means an alias silently denotes something the author
never imported, and the failure mode is a *silently unreachable match arm* —
no ambiguity error, no warning.

## Two things to fix

1. **Resolution order:** an explicitly named (and especially aliased) import
   must take precedence over a glob import of the same name; a genuine clash
   between two explicit imports should be an ambiguity error, not a silent pick.
2. **The collision itself:** `std.linalg` and `std.common.science_math.lapack`
   should not both export an enum called `LinalgError` with incompatible
   variant payloads. Renaming one is a separate, wide-ripple change (the Layer C
   one is referenced across `linalg/mod.spl`, `backend_ops.spl`,
   `torch_ndarray.spl` and many specs) and is deliberately NOT done here.

## Verification lane

`src/compiler_rust/target/debug/simple run <spec>` (debug Rust seed from
current source). Repro kept at
`scratchpad/probe8.spl` shape shown above.
