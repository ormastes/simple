<!-- codex-design -->
# RISC-V Gen2 Iterative M/Zmmul Owner — Detail Design

## Status and scope

This is the executable design for the first real, single-outstanding,
mission-critical iterative M/Zmmul owner. It consumes the already frozen
`RiscvScalarMulDivProjection` and emits one concrete RV32 or RV64
`HwSequentialModuleDef`. It does not add a second retirement owner, a generic
divider service, runtime XLEN/provider selection, raw VHDL, floating point,
atomics, vector arithmetic, or more than one outstanding operation.

Requirements: REQ-G2-012, REQ-G2-013, NFR-G2-003, NFR-G2-011,
NFR-G2-013, and NFR-G2-014.

The owner is monomorphized for exactly one projection. Therefore `W` is the
projection's `operand_width` (32 or 64), `X` is `config.xlen`, the operation is
constant, and `WORD = (X = 64 and W = 32)`. Zmmul elaboration can construct only
the four multiply operations; attempts to construct DIV/DIVU/REM/REMU fail
before a module exists.

## Public contract

Entity constructor:

`strict_riscv_scalar_muldiv_owner(name, config, lsu_config, projection)`

The `lsu_config` is used only to bind the frozen scalar-completion/v1 envelope;
the owner has no memory request port. Construction requires the exact
projection graph hash and exact scalar completion interface hash in its origin.

Inputs, all default-domain `Bits`:

| Port | Width | Meaning |
|---|---:|---|
| `clk`, `rst` | 1 | Clock and synchronous active-high reset |
| `dispatch_valid` | 1 | Request offer |
| `dispatch_lineage_valid` | 1 | Decode/event identity is meaningful |
| `dispatch_event_id`, `decode_event_id` | 64 | Must be equal and are held to completion |
| `illegal_valid` | 1 | Must be zero for this admitted provider |
| `dispatch_privilege` | 2 | Completion metadata |
| `dispatch_original_instruction`, `dispatch_canonical_instruction` | 32 | Original and exact frozen canonical instruction |
| `dispatch_instruction_length_bytes` | 3 | Must be 4 for this initial lane |
| `dispatch_pc_before`, `dispatch_pc_after` | X | Completion metadata |
| `dispatch_rd`, `rs1_index`, `rs2_index` | 5 | Must match the frozen projection |
| `rs1_value`, `rs2_value` | X | Operands; low W bits are consumed |
| `completion_ready` | 1 | Atomic completion acceptance |

Outputs are `dispatch_ready`, `completion_valid`, `completion_event_id`,
`completion_decode_event_id`, `completion_illegal_valid`, `protocol_fault`, and
every payload field of `hwir-scalar-completion/v1`. The arithmetic completion
has `rd_write = (rd != 0)`, `rd_value` as specified below, all memory fields
zero, both trap triplets zero, and both redirect fields zero. `pc_after` is the
captured dispatch value, not recomputed locally.

Handshake equations:

```text
idle_healthy     = !busy_reg && !result_valid_reg && !fault_reg
identity_match   = dispatch_lineage_valid && !illegal_valid
                   && dispatch_event_id == decode_event_id
                   && canonical == FROZEN_INSTRUCTION
                   && rd/rs1/rs2 == FROZEN_RD/RS1/RS2
                   && instruction_length_bytes == 4
dispatch_ready   = idle_healthy
dispatch_accept  = dispatch_valid && dispatch_ready && identity_match
completion_valid = result_valid_reg && !fault_reg
completion_accept= completion_valid && completion_ready
```

Ready does not depend on valid. A producer may keep `dispatch_valid` asserted
while ready is low; that is ordinary backpressure and is not a fault. Likewise,
`completion_ready` may be high before valid. On `completion_valid=1` and
`completion_ready=0`, every completion field remains byte-for-byte stable.
There is no fall-through completion and no same-edge consume-and-reaccept: a
completion acceptance makes the following cycle idle, and a new request can be
accepted on the next edge.

## Exact state

Every register resets to zero in clock domain `default`.

| Register | Width | Purpose |
|---|---:|---|
| `busy_reg` | 1 | Iteration or finalization owns the machine |
| `result_valid_reg` | 1 | Held completion is present |
| `fault_reg` | 1 | Sticky protocol/integrity fault |
| `count_reg` | `C=ceil(log2(W+1))` (6 for W32, 7 for W64) | Completed iterations, 0..W |
| `acc_reg` | `2W` | Multiply accumulator |
| `multiplicand_reg` | `2W` | Shifted multiply addend |
| `multiplier_reg` | `W` | Shifted multiply multiplier |
| `remainder_reg` | `W+1` | Unsigned restoring remainder |
| `divisor_reg` | `W+1` | Zero-extended divisor magnitude |
| `dividend_reg` | `W` | Shifted dividend magnitude |
| `quotient_reg` | `W` | Constructed unsigned quotient |
| `result_reg` | X | Final architectural result |
| `result_negate_reg` | 1 | Negate multiply product or divide quotient |
| `remainder_negate_reg` | 1 | Negate signed remainder |
| `special_reg` | 2 | 0 normal, 1 divide-by-zero, 2 signed overflow |
| `event_id_reg`, `decode_event_id_reg` | 64 | Captured identity |
| `privilege_reg` | 2 | Captured metadata |
| `original_instruction_reg`, `canonical_instruction_reg` | 32 | Captured instruction identity |
| `instruction_length_reg` | 3 | Captured length |
| `pc_before_reg`, `pc_after_reg` | X | Captured PCs |
| `rd_reg` | 5 | Captured destination |

Multiply and divide registers coexist to keep one fixed structural template.
Unused-family registers remain zero. This is intentional evidence-friendly
state, not a claim of final PPA optimization.

## HWIR representation constraint

Ordered sequential rules are priority `if/elsif` rules. The required order is:
`sticky_fault`, `completion_consume`, `finalize`, `iterate`,
`dispatch_identity_mismatch`, `dispatch_capture`. Reset dominates all rules.

Current `HwSeqValue` may assign only zero, copy, invert, or increment. Thus each
formula below is a named, single-driver `HwSignal` built from `HwCombOp`,
`HwCompareOp`, and `HwSelectOp`, and a rule copies that signal to state. The
implementation must first admit and VHDL-render these typed operations where
not already legal:

1. constants and signals through width `2W` (128 for RV64 multiply), without
   storing their values in host `i64`;
2. fixed one-bit left/right shifts and low-bit/MSB extraction without requiring
   a W-bit dynamic shift amount;
3. zero/sign extension, truncation, add, subtract, unsigned compare, and select
   for differing source/result widths explicitly declared by the operation;
4. a constant `W` usable in the C-bit equality comparison.

Fail closed with `HWIR-E-RISCV-MULDIV-OWNER-HWIR` if any primitive is absent.
Do not encode the formulas as VHDL fragments or host precomputed results.

The fixed bit/slice and arbitrary-width constant primitives are deliberately
scoped to `HwSequentialModuleDef`. They do not widen the base combinational
`HwModuleDef` constructor ABI or force unrelated strict graphs to carry empty
iterative-datapath fields.

## Request capture and common normalization

Only `dispatch_accept` captures state. It copies all completion metadata, sets
`busy_reg=1`, clears `result_valid_reg`, `count_reg`, `result_reg`, and all
unused datapath registers. Let `a = low_W(rs1_value)`, `b = low_W(rs2_value)`,
`sa=a[W-1]`, `sb=b[W-1]`, and `negW(v)=0-v modulo 2^W`.

For unsigned operands, magnitude is the operand. For signed operands,
`magnitude(v)=sa ? negW(v) : v`. Two's-complement minimum is deliberately
unchanged as an unsigned magnitude.

## Multiply: MUL, MULH, MULHSU, MULHU

Operation normalization is exact:

| Operation | A magnitude | B magnitude | Negate 2W product | Selected bits |
|---|---|---|---|---|
| `multiply_low` (MUL/MULW) | `a` | `b` | 0 | low W |
| `multiply_high_signed` (MULH) | `abs_signed(a)` | `abs_signed(b)` | `sa xor sb` | high W |
| `multiply_high_signed_unsigned` (MULHSU) | `abs_signed(a)` | `b` | `sa` | high W |
| `multiply_high_unsigned` (MULHU) | `a` | `b` | 0 | high W |

Capture initializes `acc_reg=0`, `multiplicand_reg=zext_2W(A magnitude)`,
`multiplier_reg=B magnitude`, and `result_negate_reg` from the table.

For each iteration edge while `count_reg < W`:

```text
addend       = multiplier_reg[0] ? multiplicand_reg : zero_2W
acc_next     = acc_reg + addend                 (modulo 2^(2W))
multiplicand_next = multiplicand_reg << 1       (modulo 2^(2W))
multiplier_next   = multiplier_reg >> 1         (logical)
count_next   = count_reg + 1
```

The edge performing iteration W uses `acc_next`, not stale `acc_reg`, when it
transitions to finalization. Finalization computes
`signed_product = result_negate_reg ? (0 - product_unsigned) : product_unsigned`,
then selects low or high W. For MULW, select low 32 and sign-extend bit 31 to
64. No high-half W instruction exists. For non-W results, zero-preserving bit
placement to X is exact (X=W).

Latency from request-accept edge is W iteration cycles plus one registered
finalization edge; `completion_valid` first observes high immediately after
that finalization edge. This deterministic latency is structural, not an ISA
promise.

## Divide/remainder: DIV, DIVU, REM, REMU and W forms

Signedness and result selection:

| Operation | Dividend magnitude | Divisor magnitude | Final value |
|---|---|---|---|
| `divide_unsigned` | a | b | quotient |
| `remainder_unsigned` | a | b | remainder |
| `divide_signed` | abs(a) | abs(b) | quotient negated iff `sa xor sb` |
| `remainder_signed` | abs(a) | abs(b) | remainder negated iff `sa` |

Capture sets `remainder_reg=0`, `dividend_reg=dividend magnitude`,
`divisor_reg=zext_(W+1)(divisor magnitude)`, `quotient_reg=0`, and sign flags.
It also classifies corners using original W-bit operands:

```text
divide_by_zero = (b == 0)
signed_overflow = signed_op && a == (1 << (W-1)) && b == all_ones_W
special_reg = divide_by_zero ? 1 : signed_overflow ? 2 : 0
```

`special_reg != 0` skips iteration and proceeds through the same registered
finalization edge. Divide-by-zero produces quotient `all_ones_W` and remainder
`a`. Signed overflow produces quotient `min_signed_W` and remainder zero.
These are architectural results, never traps and never protocol faults.

Normal restoring division performs exactly W iterations. On each iteration:

```text
shifted_rem = (remainder_reg << 1) | zext_(W+1)(dividend_reg[W-1])
ge          = shifted_rem >= divisor_reg             (unsigned)
rem_next    = ge ? shifted_rem - divisor_reg : shifted_rem
quot_next   = (quotient_reg << 1) | (ge ? 1 : 0)
dividend_next = dividend_reg << 1
count_next  = count_reg + 1
```

As for multiply, iteration W hands `rem_next` and `quot_next` to finalization,
not the stale registers. Signed correction is modulo 2^W. DIV/DIVU select the
corrected quotient; REM/REMU select the corrected remainder. DIVW, DIVUW, REMW,
and REMUW always sign-extend the selected 32-bit result to X=64, including
DIVUW and REMUW. Normal divide latency is W iterations plus one finalization
edge; corner latency is one finalization edge.

## Completion, priority, and fault behavior

Finalization atomically writes `result_reg`, clears `busy_reg`, and sets
`result_valid_reg`. Completion acceptance clears `result_valid_reg`, result,
and captured metadata. It never changes `fault_reg`.

`fault_reg` is reset-cleared and otherwise sticky. A fault suppresses
`dispatch_ready`, `completion_valid`, `rd_write`, and every effect-valid output;
all non-valid payload outputs are normalized to zero. Already captured state
may remain internally but cannot become architectural output.

Fault causes are deliberately narrow and falsifiable:

1. an idle healthy `dispatch_valid` whose lineage, event equality, illegal bit,
   length, instruction, or rd/rs indices do not match the frozen projection;
2. internal impossible state: `busy_reg && result_valid_reg`, count greater
   than W, normal divide with zero divisor, multiply with nonzero divide state,
   or divide with nonzero multiply state;
3. structural/hash/config/provider substitution detected at construction.

Cause 3 rejects construction with a stable diagnostic and creates no RTL.
Causes 1–2 set the runtime sticky output. Valid held during ordinary
backpressure, early ready, reset, divide-by-zero, overflow, `rd=x0`, and input
changes after an accepted request are not faults.

## Structural identity and emitted provenance

The module node is `HwNodeId.module_root(name)`; the plan is
`HwNodeId.child(name, "sequential")`. Stable node identities cover every
register, ordered rule, output, and projection pin. Constants and combinational
operations are ordered rows in the enclosing structural hash; they do not
falsely claim independent child node IDs.
The origin source name contains:

```text
riscv.scalar.muldiv.iterative-owner/v1
|projection=<projection.structural_sha256>
|completion=<completion.structural_sha256>
|algorithm=shift-add+restoring
|W=<32|64>|X=<32|64>|operation=<frozen operation>
```

Canonical hashing must include all guards (including output guards), operation
widths, priority order, and the exact child graph. Equal inputs emit
byte-identical VHDL. No receipt may call this owner qualified without the
generated-VHDL tests in the companion plan.

## Implementation handoff gates

The owner is done only when all sixteen architectural M operations across RV32
and RV64 applicability (including the eight RV64 W encodings) are generated
from the projection, Zmmul rejection is proven, generated VHDL passes GHDL,
backpressure stability and sticky faults pass, host oracle and RTL agree on
directed and deterministic randomized vectors, and the self-hosted qualified
route records the exact owner graph hash. A host evaluator alone is not owner
evidence.
