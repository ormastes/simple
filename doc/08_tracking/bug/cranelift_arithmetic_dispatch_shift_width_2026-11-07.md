# Cranelift power, floating remainder, and shift destination width

Status: source repaired; independent source review approved; runtime verification pending.
No source-matched admitted pure-Simple producer is available to execute the
authored regressions. No native or production-readiness PASS is claimed.

## Confirmed source defects

The baseline adapter blob is `0716f9ae50ded1c5e8bd7b392fdcf83906045b41`,
also present in release snapshot `3362849eda19d05b6e9b4a3aa0782681da2e2471`.
This follow-up preserves the reviewed narrow arithmetic and legal-I32 float
cast repairs from PR #7443.

- `MirBinOp.Pow` had no dispatch arm and fell through to `iadd`. A runtime
  parameter helper `base ** exponent`, called with 2 and 3, therefore emitted
  addition and produced 5 instead of 8. Float power also reached integer IR.
  The repair emits wrapping I64 exponentiation by squaring for integers and
  calls the existing `rt_math_pow` floating runtime provider with its actual ABI.
  Reusing `__simple_pow` would interpret high-bit U64 exponents as negative
  and perform overflowing signed C multiplication; the emitted loop consumes
  unsigned exponents with logical shifts and preserves the current zero result
  for signed negative exponents.
- Floating remainder was excluded from numeric promotion and always emitted
  `srem`/`urem`. A parameter helper computing 5.5 % 2.0 therefore emitted an
  integer instruction on floating operands. The repair promotes operands and
  calls the existing platform `fmod` ABI. F32 arguments promote to F64 for
  that ABI, then the result demotes to F32; floating power uses the same
  typed import mechanism. No runtime or vendored provider source changes.
- Shifts execute in the adapter's I64 SSA lane. Their implicit hardware count
  mask was therefore 63 for every destination, whereas the LLVM owner defines
  `count & (destination_bits - 1)`. For an I8 MIR destination, starting
  at 1 and shifting by 8 produced zero instead of 1. The repair passes the
  actual MIR destination type to binary dispatch and masks the count before
  emitting the shift.

Shift tests deliberately distinguish provenance. Ordinary binary expressions
and local compound assignments currently default to an I64 MIR destination,
even when their LHS is narrow. The local compound-assignment operator mapping
also omits shifts. This repair tests explicit typed MIR through the actual
Cranelift instruction translator and JIT provider instead of claiming that
a source annotation establishes a narrow shift. Masking solely by the LHS type
would change a wide case incorrectly. The prior
`test/fixtures/compiler/cranelift_narrow_binop/wrap_signed.spl` fixture's
15 cases are **UNQUALIFIED SOURCE EXPECTATIONS**. Neither the intended
source-level width contract nor the actual producer's MIR destinations were
established here; I64 inference may be the intended language contract. That
fixture cannot establish narrow BinOp acceptance without both the source
width contract and observed MIR. The new typed-MIR shift test isolates the
backend contract and makes no claim about source-level width inference.

The generic arithmetic fallback now fails explicitly instead of silently
substituting addition for future unsupported operations.

## Reproducing and prevention tests

- `test/01_unit/compiler/backend/cranelift_shift_width_spec.spl` invokes
  production instruction translation on explicit typed MIR, finalizes real
  callable Cranelift JIT code, then executes 66 shift checks across all eight
  integer kinds, both directions, width/width-plus-one/negative/zero counts,
  and wide MIR destinations with narrow source metadata.
- `test/fixtures/compiler/cranelift_arithmetic/power_remainder.spl` contains
  33 integer/F32/F64/mixed-type power and remainder checks, including parity,
  zero exponents, the existing intrinsic's negative-exponent result, terminal
  exponent-one control, signed remainders, unsigned high-bit remainder,
  high-bit U64 exponents, and wrapping integer powers.
- `test/02_integration/compiler/backend/cranelift_arithmetic_spec.spl`
  requires explicit `SIMPLE_BINARY`, compiles the source fixture with Cranelift,
  then checks actual execution exit codes and completion markers.

The mathematical shift oracle masks the count by the declared destination
width, shifts the source value with arithmetic/logical interpretation, and
observes the result's I64 representation. Power expectations follow repeated
multiplication modulo 2^64, including explicit overflow controls. Remainder
uses truncation toward zero
and the dividend's sign. The tests remain unexecuted pending an admitted
source-matched producer and the applicable compiler/core/MCP verification.

## Unresolved audit boundaries

`CheckedBinOp` delegates ordinary binary emission in both Cranelift and LLVM.
No source-lowering producer or complete overflow-result contract was found
in this scoped audit. Its distinct checked-overflow behavior is unresolved;
this change does not invent a trap, tuple, or wrapping contract for it.
Signedness choices for ordinary division and comparisons match the existing
LLVM owner; no additional defect was established by source review alone.
