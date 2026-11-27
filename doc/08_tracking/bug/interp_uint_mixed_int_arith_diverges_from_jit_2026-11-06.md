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
exception carriers and generic intrinsic/bounds-check arguments. The candidate threads each
actual operand's unsigned metadata through existing numeric conversion helpers.
Field storage retains its verbatim/no-sticky-value-map contract, signed operands
still sign-extend and pointers keep their existing representation.

Same-width wrapping is an existing contract, documented at
`doc/05_design/platform/structural_compute/execution_profile_contract_v1.md:219`
and asserted by `test/01_unit/bugs/jit_narrow_unsigned_wrap_spec.spl`.
The wider-variable contrast is pinned by `u8_times_wider_int_widens_spec.spl`.
The common-carrier implementation decision above was explicitly approved
for this repair. It aligns the narrow unsigned wrapping and wider signed-peer
profile without claiming a new general language promotion/overflow rule.
In-range literals and broader mixed-policy cases remain residuals. Native and
interpreter results must be compared before any acceptance claim.

Executable MIR regression:
`test/01_unit/compiler/mir/same_width_unsigned_binop_spec.spl` calls the real
binary expression lowerer with typed locals, checks all nine width/operator
pairs, exact comparison operand types in both directions for all six comparison
operators, and negative wider/signed/nonarithmetic controls. Native regression:
`test/fixtures/compiler/same_width_unsigned_binop/main.spl` widens the completed
operation to i64 before returning and checks nine overflow results, a mixed-width control, comparison bounds and
negative peers, chained wrapping, and implicit return/let/call/field/index/text
consumers, signed call controls, negative-peer division/remainder and branch
joins, global stores and unary/match consumers and signed i64 controls and word-range bounds (42 checks). Both are **UNRUN**, because no admitted full test CLI is
available and disk capacity precludes a new build. Existing green evidence is
not rerun or borrowed as native qualification of this patch.

Required admission: current-source core/compiler/lib/MCP/LSP checks, executable
MIR spec, LLVM and Cranelift fixture compilation/execution with exact42-check
stdout, the same fixture through the admitted interpreter with an exact
result/output differential, and an intentional wrong-expectation negative
control. Retain source,
producer/runtime/tool identities and actual exit status. Keep status
`fix-implemented-verification-pending`; no fixed/done promotion is justified.

The first source review rejected the original candidate because a new U8 sum
compared with an i64 bound256 truncated the bound to0. Follow-up source audit
also found unsigned-blind implicit consumers. The expanded repair and tests
address these findings; no second review or runtime PASS is implied here.
`test/01_unit/compiler/backend/narrow_unsigned_consumer_widening_spec.spl`
executes actual LLVM owners for normal/terminator/indirect calls, verbatim field
storage, both global-store routes, raw GEP/offset indexing, unary/switch/exception
carriers and matching-carrier SSA joins, with signed controls and all three
narrow widths. It remains UNRUN. Generator tests now own a real positive
LlvmIRBuilder handle and complete typed function/CFG context; streamed calls
and global stores use that owned handle rather than zero or a dummy writer.

## Cycle-2 review disposition and PHI residual (2026-11-08)

The second review also returned FAIL. Checks for unsigned unary negation and
complement incorrectly expected wide signed results. The actual Unary MIR
arm already uses the operand type; corrected checks require u8 results56/55,
with signed-i64 controls-200/-201 and actual unary-lowering type assertions.
Boolean Not is unchanged. Common promotion now requires both local types to
be explicitly present. Cycle 3 excluded Is/IsNot based on a stale mapping premise;
the Astra correction below supersedes that exclusion.

The speculative mixed-width PHI widening change was removed. The actual LLVM
function path first uses typed alloca SSA in both bootstrap and normal modes;
its already unsigned-aware stores widen normal branch values safely. A direct
intrinsic or rejected-alloca legacy fallback with mixed physical widths remains
unqualified: casting inside a merge before phi is invalid placement. Such a
repair requires predecessor conversions, not an admitted-looking synthetic
merge test. Matching-width PHI tests now build a real CFG; no mixed-width PHI
fix or execution is claimed. No third review has run; review capacity is
currently blocked, and the source candidate must not land without approval.

Direct MIR producers are covered too: sparse integer matches widen a proven
narrow unsigned scrutinee before comparing its i64 keys; existing word-carrier
range loops widen proven narrow start/end values (and stepped-range operands)
without changing narrow loop-carrier policy. The generic bounds-check intrinsic
now preserves source signedness. Actual MIR match and LLVM bounds-intrinsic
regressions cover these bypasses; a plain range-bound case is included in the
42-check native/interpreter fixture. All remain UNRUN.

The positive fixture deliberately excludes implicit integer-to-f64 call
coercion. Cranelift's existing `cl_call_abi_mismatch` requires matching register
classes and rejects that raw argument shape unless conversion is explicit.
This repair does not change the floating call ABI policy.


## Astra FAIL disposition — source cycle 4 (2026-11-08)

Astra reviewed exact draft head9932323be75d2d44bc37ba1c078c4e4f6bab6409 and
returned FAIL with two P1 findings. A declared i64 binding copied a narrow
unsigned initializer without widening, so MIR claimed I64 while LLVM retained
i8; later comparisons truncated wide bounds. The Let boundary now explicitly
casts known U8/U16/U32 initializers into declared I64/U64 carriers before Copy,
while preserving the existing raw optional-scalar exception. Actual HIR Let
lowering regressions require a widening Cast, a wide-to-wide Copy and later
wide Lt/Eq/Ne operands; LLVM generator tests cover that sequence.

The current generic operator owner maps numeric Is/IsNot to Eq/Ne, contrary
to the stale enum-pattern comment and cycle-3 exclusion premise. Those numeric
operators now share the proven-integer common-carrier gate; type tests and
qualified enum-pattern handling remain unchanged. MIR tests assert Eq/Ne and
wide operands in both directions; generator and native fixture cases include
456-vs-200 truncation, high-bit 200-vs-minus56, and equal-value controls.

The fixture now has56 discriminating checks. All56 native/interpreter checks,
MIR/IR specs and required core/MCP/fixedpoint/cachehash qualification remain
UNRUN. This is source cycle4 of the six-cycle budget, after two Opus FAILs and
one Astra FAIL. The next exact head requires Astra acceptance; PR7847 remains
draft, verification pending, and must not land over these findings.
