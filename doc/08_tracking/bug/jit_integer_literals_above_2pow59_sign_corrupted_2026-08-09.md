# JIT corrupts every integer literal that needs 61 bits or more

Status: OPEN — found 2026-08-09 by the multi-engine differential harness
(`scripts/check/check_engine_differential.spl`) on its first run.
Binary under test: `bin/release/x86_64-unknown-linux-gnu/simple`, sha256
prefix `166c622b30c2257c`.

## Summary

Under the Cranelift JIT — which is the **default** engine for `bin/simple run`
— an integer literal at or above `2^60` is silently miscompiled. The
interpreter is correct for every value. There is no warning, no error and no
crash: the program runs to completion and prints a wrong number.

## Measured

Probe: literals printed directly and passed through an identity function.

| literal | interpret | jit |
|---|---|---|
| `42` | 42 | 42 |
| `1099511627776` (2^40) | 1099511627776 | 1099511627776 |
| `576460752303423488` (2^59) | 576460752303423488 | 576460752303423488 |
| `1152921504606846976` (2^60) | 1152921504606846976 | **-1152921504606846976** |
| `4611686018427387904` (2^62) | 4611686018427387904 | **0** |
| `9223372036854775807` (i64::MAX) | 9223372036854775807 | **-1** |
| `-9223372036854775807` | -9223372036854775807 | **1** |

`2^59` is correct and `2^60` is not, so the cutoff is exactly **61 bits of
signed magnitude**.

## Mechanism (inferred, consistent with every row)

The values are exactly what a **61-bit tagged immediate** produces when the
remaining bits are sign-extended back into an i64 — i.e. a 3-bit tag stolen
from the low end, leaving 61 bits, with no range check on the literal:

- `2^60` sets the sign bit of a 61-bit field, so it reads back negative with
  the same magnitude.
- `i64::MAX` is all-ones in 61 bits, which sign-extends to `-1`.
- `2^62` has no bits left inside the field at all, so it reads back `0`.

This is the same `<< 3` tagged-pointer family as the documented
`list.get` shift defect; here it corrupts the literal on the way IN rather
than the element on the way out.

## Why no existing test catches it

`bin/simple test` pins every child spec to the interpreter engine, and a spec
file (top-level `describe`/`it`, no `fn main`) de-JITs regardless because
`describe`/`it`/`expect` are Rust interpreter intrinsics with no codegen
lowering. So the entire spec corpus is structurally blind to this, and will
stay green through it. See
`doc/08_tracking/bug/jit_test_suite_blind_spot_2026-07-30.md`.

Example-based tests also naturally use small numbers, which round-trip fine —
the defect only appears above 2^59, a range no existing example exercises.

## Blast radius

Any JIT-lane code with a large literal constant: hash seeds (FNV/xxHash
offsets and primes are routinely > 2^60), bitmask constants, `i64::MAX`
sentinels used as "unset"/min-search initializers, timestamps in nanoseconds
(current epoch-ns is ~1.7e18, **above** the safe range), and fixed-point
scaling factors. A `i64::MAX` sentinel becoming `-1` is especially dangerous:
it inverts every `if x < best` comparison in a min-search.

## Reproduce

    bin/simple run scripts/check/check_engine_differential.spl
    # or narrowed:
    DIFF_FILTER=i64 bin/simple run scripts/check/check_engine_differential.spl

Fixture: `test/fixtures/engine_differential/i64_boundary_values.spl`.

## Not yet done

- Root-caused to the literal lowering site in the Cranelift path (the 61-bit
  field is inferred from the value table above, not yet read off the code).
- Not checked whether the **native/LLVM** lane shares the defect.
- No fix. The right fix is presumably to box a literal that does not fit the
  tagged immediate, rather than truncating it; failing closed with a
  diagnostic would also be an improvement over the current silent wrong
  answer.
