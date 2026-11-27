# Cranelift cast width and signedness

Status: source repaired; independent source review approved; runtime verification pending.
The native regressions have not executed with an admitted, source-matched
pure-Simple producer. No compiler, fixture, or production-readiness PASS is claimed.

## Defects established by source review

The Cranelift adapter keeps integer SSA values in an I64 representation.
`cl_translate_cast` previously returned the source unchanged for equal-width
integer casts and widening casts. This loses destination signedness:
`u8(255) as i8` remains 255 instead of -1; `i8(-1) as u8` remains -1
instead of 255; `i8(-1) as u16` remains -1 instead of 65535.

Float-to-integer casts always selected `fcvt_to_sint` and returned its
target-width result directly. Narrow destinations therefore leaked I8/I16/I32
SSA values into an I64 lane. Unsigned-valid high-bit inputs, including
2147483648.0 to U32 and 9223372036854775808.0 to U64, selected a signed
conversion that cannot represent them.

The repair normalizes every sub-64-bit integer destination by reducing the
I64 input to its target width, then sign- or zero-extending to I64. Float
conversion selects the existing signed/unsigned SFFI operation and extends
the result to I64. Bool retains its I64 representation;
Char retains its U32 representation. The committed signed narrow arithmetic
repair and float-typed integer-constant repair remain intact.

Pinned-provider review found an additional boundary: Cranelift 0.116.1's x64
lowering accepts I8/I16 float-conversion IR types, then passes their sizes
to an instruction emitter restricted to I32/I64 (`x64/lower.isle`,
`x64/inst.isle`, and `x64/inst/mod.rs::xmm_to_gpr`). The earlier direct-small
conversion design was rejected before landing. I8/I16 destinations now
convert through legal I32, extend to I64, and compare that integer with its
destination-normalized value. A mismatch branches to an explicit trap;
success continues with the normalized I64. This preserves truncation before
the range check: -128.75 to I8 is -128, 255.75 to U8 is 255, and -0.75 to U8
is zero, while 128.0 to I8 and 256.0 to U8 trap. The I32 conversion itself
retains NaN/infinity and wider overflow traps. I32/I64 destinations convert
directly at their existing widths.

## Prevention tests

- `test/fixtures/compiler/cranelift_narrow_cast/integer_width_matrix.spl`:
  all 64 pairs of I8/U8/I16/U16/I32/U32/I64/U64 with boundary values and
  positive controls, for 128 assertions.
- `test/fixtures/compiler/cranelift_narrow_cast/float_to_integer.spl`:
  F32/F64 to all eight integer types, with negative signed fractions,
  unsigned high-bit values, positive fractions, and fractional destination
  boundaries, for 48 assertions.
- `test/fixtures/compiler/cranelift_narrow_cast/float_to_small_integer_traps.spl`:
  a valid execution control and 40 separately selected range/nonfinite cases:
  F32/F64 to I8/U8/I16/U16, testing overflow, underflow, NaN and both infinities.
- `test/02_integration/compiler/backend/cranelift_narrow_cast_spec.spl`:
  requires an explicit `SIMPLE_BINARY`, builds all three fixtures with
  Cranelift, executes positive cases, and runs each negative case separately.
  Negative checks require the selected case's entry marker, a nonzero exit,
  no timeout, and no marker indicating that the invalid cast returned.

Harness review also identified an existing process-facade inconsistency:
`process_run_timeout_unix` reports a seconds-suffixed timeout marker, while
`process_bounded_timed_out` recognizes the corresponding milliseconds suffix.
The negative fixture runner explicitly rejects either marker prefix as well
as using the shared classifier. Unifying those facade contracts remains
separate follow-up work; the cast repair does not change that owner.

The integer expectations follow arithmetic independently of the adapter:
take the source mathematical value modulo 2^destination_width, subtract
2^destination_width when a signed destination has its high bit set, then
observe the resulting I64 bit pattern. Signed inputs use -1; unsigned inputs
use their maximum value; every pair also tests +1. Float expectations use
truncation toward zero for in-range fractions and exactly representable
powers of two at unsigned signed-boundary crossings.

Parameters force evaluation in generated code. Each helper casts and widens
directly, avoiding an annotated narrow temporary that could normalize an
incorrect result before observation. Runtime acceptance requires rebuilding
the affected producer and executing this integration spec and applicable
compiler/core/MCP checks. Static review and whitespace checks do not replace
that evidence.
