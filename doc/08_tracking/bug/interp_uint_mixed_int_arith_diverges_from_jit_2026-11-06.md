# Interpreter `uN op Int` arithmetic vs JIT: the JIT is the divergent lane, no HIR rule to copy (2026-11-06)

Status: fix-implemented-verification-pending — narrow source candidates exist; native acceptance and mixed/literal promotion residuals remain open. The original round-10 interpreter premise was disproven; no interpreter rule was changed.

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


## 2026-11-08: pure-Simple same-width MIR candidate, verification pending

The host MIR lowerer used `infer_binop_type`'s i64 default for unsigned
arithmetic. LLVM then correctly widened both operands to that incorrect
result width before adding/subtracting/multiplying. A backend-only mask would
leave the MIR type wrong. The candidate preserves the operand type only for
host `+ - *` with two actual MIR locals of exactly the same U8, U16 or U32
kind. Other host integer numeric operations involving at least one narrow
unsigned operand now promote both integer operands to a common carrier: i64
with signed/narrow peers, U64 with a U64 peer. Their existing result inference
is retained. This explicit common-operand rule preserves negative signed
peers in division/remainder and bounds beyond the narrow width in comparisons.
Same-width unsigned wrapping remains typed at its original width, including
chains. GPU, float, pointer, tagged-runtime/unknown operands and the separate
U64-versus-I64 policy remain unchanged. In-range literal wrapping and broader
mixed-promotion residuals remain open; this is not the complete broad bug.

The new narrow SSA values also exposed signed-default widening at LLVM call,
aggregate field/global stores, raw GEP/offset indices, unary operands, switch/
exception carriers and SSA-phi consumers. The candidate threads each
actual operand's unsigned metadata through existing numeric conversion helpers.
Field storage retains its verbatim/no-sticky-value-map contract, signed operands
still sign-extend and pointers keep their existing representation.

Same-width wrapping is an existing contract, documented at
`doc/05_design/platform/structural_compute/execution_profile_contract_v1.md:219`
and asserted by `test/01_unit/bugs/jit_narrow_unsigned_wrap_spec.spl`.
The wider-variable contrast is pinned by `u8_times_wider_int_widens_spec.spl`.
No new general promotion or overflow policy is selected here.

Executable MIR regression:
`test/01_unit/compiler/mir/same_width_unsigned_binop_spec.spl` calls the real
binary expression lowerer with typed locals, checks all nine width/operator
pairs, exact comparison operand types in both directions for all six comparison
operators, and negative wider/signed/nonarithmetic controls. Native regression:
`test/fixtures/compiler/same_width_unsigned_binop/main.spl` widens the completed
operation to i64 before returning and checks nine overflow results, a mixed-width control, comparison bounds and
negative peers, chained wrapping, and implicit return/let/call/field/index/text
consumers, signed call controls, negative-peer division/remainder and branch
joins, global stores and unary/match consumers (40 checks). Both are **UNRUN**, because no admitted full test CLI is
available and disk capacity precludes a new build. Existing green evidence is
not rerun or borrowed as native qualification of this patch.

Required admission: current-source core/compiler/lib/MCP/LSP checks, executable
MIR spec, LLVM and Cranelift fixture compilation/execution with exact40-check
stdout, and an intentional wrong-expectation negative control. Retain source,
producer/runtime/tool identities and actual exit status. Keep status
`fix-implemented-verification-pending`; no fixed/done promotion is justified.

The first source review rejected the original candidate because a new U8 sum
compared with an i64 bound256 truncated the bound to0. Follow-up source audit
also found unsigned-blind implicit consumers. The expanded repair and tests
address these findings; no second review or runtime PASS is implied here.
`test/01_unit/compiler/backend/narrow_unsigned_consumer_widening_spec.spl`
executes actual LLVM owners for normal/terminator/indirect calls, verbatim field
storage, both global-store routes, raw GEP/offset indexing, unary/switch/exception
carriers and SSA joins, with signed controls and all three
narrow widths. It remains UNRUN. The SSA transform's real `ssa_phi_instruction`
producer emits incoming locals without conversion; the backend therefore owns
widening incoming scalar values to its declared phi carrier.
