# unsigned_div64 Arithmetic Overflow for Large i64 Values - 2026-05-21

## Summary

`unsigned_div64` in `src/lib/hardware/rv64gc_rtl/mul_div.spl` produces wrong
results when operand `a` is large (MSB set, i.e., negative as signed i64).

## Failing Tests

In `test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl`:

- `AC-1: DIVU of large unsigned values produces correct quotient`
  - Input: `0xFFFF_FFFF_FFFF_FFFE / 2`
  - Expected: `0x7FFF_FFFF_FFFF_FFFF`
  - Actual: incorrect (integer overflow in the `a_neg=1, b_neg=0` branch)

- `AC-1: REMU of large unsigned values produces correct remainder`
  - Input: `0xFFFF_FFFF_FFFF_FFFF % 3`
  - Expected: `0`
  - Actual: incorrect (same overflow)

## Root Cause

In `unsigned_div64`, the branch handling `a_neg=1, b_neg=0` (i.e. `a` has
MSB set but `b` doesn't) does signed arithmetic on what should be treated as
unsigned 64-bit values. The negation step (`-a`) overflows for `a = 0x8000_0000_0000_0000`
and produces wrong quotients and remainders for any `a >= 0x8000_0000_0000_0000`.

Relevant source: `src/lib/hardware/rv64gc_rtl/mul_div.spl`, function `unsigned_div64`.

## Impact

DIVU and REMU M-extension instructions produce wrong results for dividend
values with MSB set (i.e., unsigned values >= 2^63). This affects any RV64 code
using unsigned division on large values, which is common in address computation
and Linux kernel arithmetic.

## Proposed Fix

Use a bit-manipulation approach that avoids sign-extension pitfalls:
- For DIVU: implement using right-shift + repeated subtraction or use the
  two's-complement identity `a_unsigned = a_signed + 2^64` when MSB is set.
- Alternatively, expose a native `rt_u64_div` extern that calls `(u64)a / (u64)b`
  in Rust/C to avoid the issue entirely in interpreter mode.

## Status

Open. Discovered 2026-05-21 while fixing import errors in `core64_integration_spec.spl`.
The spec correctly tests the DIVU/REMU behavior; the bug is in the library implementation.
