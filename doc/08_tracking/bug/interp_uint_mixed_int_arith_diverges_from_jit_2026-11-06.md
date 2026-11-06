# Interpreter `uN op Int` arithmetic vs JIT: the JIT is the divergent lane, no HIR rule to copy (2026-11-06)

Status: OPEN - the premise of the round-10 task does not hold; no interpreter change made.

## Measurement (seed from release tip, `SIMPLE_EXECUTION_MODE=jit`)

`val a: u8 = 250; val b: u8 = 10; val x: u32 = 4000000000; val y: u32 = 500000000`

| expr | JIT | interpreter (pinned by u32_wrap_arith_spec / u8_times_wider_int_widens_spec) |
|---|---|---|
| `a + b` (u8+u8) | 260 | 4 (wraps) |
| `b - a` | -240 | 16 (wraps) |
| `x + y` (u32+u32) | 4500000000 | 205032704 (wraps) |
| `a + 10`, `a * 2` | 260, 500 | 4, 244 (wraps) |
| `val v: u8 = a + b` | 4 (truncated at the typed store) | 4 |

The JIT performs NO modulo-2^width wrap on `+ - *` for narrow unsigned operands,
even u8+u8 with both sides statically u8. It only truncates when the result is
stored into a narrow typed slot. So `b + 100` = 300 and `b * s` = 600 are not the
product of a type rule that treats the literal as i64; they are the absence of any
wrap.

## Why no interpreter rule can match

`hir/lower/expr/operators.rs::lower_binary` types a mixed binary as the LEFT operand
type (only u8/u16 `<<` is promoted to I64). So `b * s` (s: i64) and `b + 100` are
both typed u8 by HIR; codegen then does not wrap. The probe's `b + 100` (JIT 300)
and `u8_times_wider_int_widens_spec` "still wraps u8 with an in-range operand"
(`x: u8 = 200u8; x + 100` == 44) are the SAME expression with opposite required
results. A value- or literal-based rule in `uint_arith_wrap_width` cannot satisfy
both, and the interpreter cannot see static types of runtime `Value::Int`.

## Verdict

The interpreter wrapping is the documented, spec-pinned semantics
(`interpreter_u32_wrap_subtraction_2026-05-01`, u32_wrap_arith_spec, hkdf/crc32/
siphash collateral). The JIT/native lane lacks result truncation for `uN op uN`
and `uN op literal`. The correct fix is in codegen: truncate/mask `Binary` results
whose HIR type is U8/U16/U32, and decide `uN op i64` promotion in HIR typing, which
needs a deliberate language-rule decision (left-type vs wider-type). That needs a
seed rebuild and a JIT-vs-interpreter differential and was not done this round.
Interpreter left unchanged: changing it would break the pinned specs above.

## Update 2026-11-06: JIT fixed (codegen/instr/core.rs wrap_narrow_unsigned_arith)

Cranelift BinOp `+ - *` now masks to the dest vreg's static width (u8/u16/u32) when the
right operand is the same narrow type or an in-range integer literal. A wider non-literal
operand (`b * s`, s: i64) or out-of-range literal (`a * 300`) is not masked, matching the
interpreter (HIR types the op as the LEFT operand; no doc states a promotion rule, so it
was not changed). Probe (`run`, SIMPLE_EXECUTION_MODE=interpreter vs jit) is now identical:
u8 `4 116 224`, lit `44 144`, u16 `4464 15536 17920`, u32 `205032704 794967296 1321730048`,
mixed `180 60000`. Note `simple test` runs specs in the interpreter regardless of the env
var, so JIT proof is via `run` of a probe file. Cost: one `and` with immediate per narrow op.
LLVM backend not changed.
