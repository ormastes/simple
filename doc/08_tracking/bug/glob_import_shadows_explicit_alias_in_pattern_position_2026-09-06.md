# Glob import shadows an explicit `use ... as` alias in pattern position

- **Date:** 2026-09-06
- **Status:** fixed 2026-09-08 (`interpreter_patterns.rs`)
- **Area:** compiler / name resolution (Rust seed interpreter)
- **Found by:** scilib-ports lane, closing
  `test/03_system/plan_acceptance/scilib_port_lapack_spec.spl`
  (`REQ-SCILIB-LAPACK-08`).

## Symptom

`test/03_system/plan_acceptance/scilib_port_lapack_spec.spl` imports

```
use std.common.science_math.lapack.{ LinalgError as LapackError, ... }
use std.linalg.*
```

and then matches

```
case Err(LapackError.Singular(row: _)):
```

The arm never matches, so the example falls through to `case _:` and its
`expect(false).to_equal(true)` fires. The value really is
`Err(LinalgError.Singular(row: 1))` — `singular.is_err()` is `true` and the
payload is correct.

## Root cause

Two distinct enums are named `LinalgError`:

- `src/lib/common/science_math/lapack.spl:38` — `Singular(row: i64)`,
  `BadArgument(arg: i64)`, `NotConverged(iterations: i64)`, ...
- `src/lib/nogc_async_mut/linalg/linalg_core.spl:8` — `DimensionMismatch`,
  `Singular` (**no payload**), `NotConverged` (no payload).

The second one arrives through the glob `use std.linalg.*`. In pattern
position the glob wins over the explicit, aliased, single-name import, so
`LapackError.Singular(row: _)` is resolved against the payload-free variant
and can never match a `Singular(row: ...)` value.

An explicit named import must take precedence over a glob import. It does in
the ordinary expression/type positions — the same file's other uses of
`LapackInfo`, `Pivot`, `Workspace` resolve correctly.

## Minimal reproduction

```
use std.common.science_math.lapack.{ LinalgError as LapackError, MockLapackProvider }
use std.linalg.*

fn main():
    val singular = MockLapackProvider().gesv(2, [1.0, 1.0, 2.0, 2.0], [1.0, 2.0])
    print "is_err=" + singular.is_err().to_text()      # true
    match singular:
        case Err(LapackError.Singular(row: r)):
            print "matched row=" + r.to_text()
        case _:
            print "no-match"                            # <-- taken
```

Dropping the `use std.linalg.*` line (or importing `LinalgError` directly
without the alias) makes the same match succeed and print `matched row=1`.

## Impact

`REQ-SCILIB-LAPACK-08` cannot pass while this holds. The oracle is correct and
must not be weakened: the `Singular` error path IS produced correctly by
`MockLapackProvider.gesv` (pivoted Gaussian elimination,
`src/lib/common/science_math/lapack.spl:165`), the spec simply cannot observe
it.

## Resolution

`pattern_enum_name_matches` now resolves a qualified pattern's local name
through the imported `Value::EnumType` binding before comparing it with the
runtime enum's canonical name. The focused Rust regression plants a conflicting
glob name and proves both the positive alias match and the adjacent negative
case. After removing the unrelated duplicate SIMD exports that prevented the
test binary from linking, the regression passed (`1 passed`, 3,935 filtered),
and the unchanged LAPACK plan-acceptance spec passed 10/10 on the rebuilt hosted
compiler before its additional false-green assertions were strengthened.
