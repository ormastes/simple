# Integers needing 61+ bits are corrupted: JIT everywhere, native inside containers

Status: OPEN — found 2026-08-09 by the multi-engine differential harness
(`scripts/check/check_engine_differential.spl`) on its first run.
Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple`, sha256
prefix `166c622b30c2257c`.

## Summary

An integer at or above `2^60` is silently corrupted. There is no warning, no
error and no crash: the program runs to completion and prints a wrong number.
The interpreter is correct for every value.

The three-lane comparison splits this into **two distinct defects**, which is
the finding a two-lane (interpret vs JIT) comparison would have merged:

| | scalar local / arg | element stored in a list |
|---|---|---|
| interpret | correct | correct |
| **jit** | **CORRUPT** | **CORRUPT** |
| **native (LLVM AOT)** | correct | **CORRUPT** |

- **Defect A — JIT scalars.** JIT-only. A plain `val`/argument holding a large
  integer is already wrong before any container is involved.
- **Defect B — container boxing.** Shared by JIT **and** native, so it lives
  in the common boxed-value representation rather than in either codegen. This
  is the more important of the two: native gets scalars right and still
  corrupts the same values on the way into a list.

## Measured

Fixture: `test/fixtures/engine_differential/i64_boundary_values.spl`.
`p*` are scalars through an identity fn; `boxed_*` are the same values read
back out of a `[i64]`.

| | interpret | jit | native |
|---|---|---|---|
| `small=42` | 42 | 42 | 42 |
| `p60` (2^60) | 1152921504606846976 | **-1152921504606846976** | 1152921504606846976 |
| `p62` (2^62) | 4611686018427387904 | **0** | 4611686018427387904 |
| `imax` (i64::MAX) | 9223372036854775807 | **-1** | 9223372036854775807 |
| `inegmax` | -9223372036854775807 | **1** | -9223372036854775807 |
| `boxed_p60` | 1152921504606846976 | **-1152921504606846976** | **-1152921504606846976** |
| `boxed_p62` | 4611686018427387904 | **0** | **0** |
| `boxed_imax` | 9223372036854775807 | **-1** | **-1** |

A separate narrowing probe established the cutoff exactly: `2^59`
(576460752303423488) is correct on the JIT, `2^60` is not. `2^40` is correct.

## Mechanism (inferred; consistent with every row)

The wrong values are exactly what a **61-bit tagged immediate** yields when
the surviving bits are sign-extended back to i64 — a 3-bit tag stolen from the
low end, with no range check on the value:

- `2^60` sets the sign bit of a 61-bit field, so it returns negative with the
  same magnitude.
- `i64::MAX` is all-ones across 61 bits, sign-extending to `-1`.
- `2^62` retains no bits inside the field, returning `0`.

Native agreeing with the interpreter on scalars but with the JIT on list
elements is what localizes Defect B to the shared boxing path: native only
boxes when a value enters a container, and that is precisely where it starts
losing bits.

This is the same `<< 3` tagged-pointer family as the documented `list.get`
shift defect, but here the value is destroyed on the way IN rather than
mis-read on the way out.

## Why no existing test catches it

`bin/simple test` pins every child spec to the interpreter, and a spec file
(top-level `describe`/`it`, no `fn main`) de-JITs regardless because
`describe`/`it`/`expect` are Rust interpreter intrinsics with no codegen
lowering. The spec corpus is structurally blind to both defects and will stay
green through them. See
`doc/08_tracking/bug/jit_test_suite_blind_spot_2026-07-30.md`.

Example-based tests also use small numbers, which round-trip fine — nothing
appears below 2^59.

## Blast radius

Any large integer constant on a compiled lane: hash seeds and primes
(FNV/xxHash offsets exceed 2^60), bitmasks, `i64::MAX` sentinels used as
"unset" or as a min-search initializer, and **nanosecond timestamps**
(current epoch-ns is ~1.7e18, well above the safe range).

Defect B is the dangerous one in practice because it needs no large literal in
the source — any large value computed at runtime is corrupted merely by being
stored in a list, on the **native** lane that ships. An `i64::MAX` sentinel
becoming `-1` inverts every `if x < best` comparison in a min-search.

## Reproduce

    bin/simple run scripts/check/check_engine_differential.spl
    # narrowed (native lane needs a full native-build, several minutes):
    DIFF_FILTER=i64 bin/simple run scripts/check/check_engine_differential.spl

## Not yet done

- Not root-caused to a specific lowering site; the 61-bit field is inferred
  from the value table, not yet read off the code.
- No fix. A value that does not fit the tagged immediate should be heap-boxed
  rather than truncated; failing closed with a diagnostic would still beat the
  current silent wrong answer.
