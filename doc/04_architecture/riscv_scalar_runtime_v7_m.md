<!-- codex-architecture -->
# Runtime scalar pipeline V7: unified dynamic IM owner

## Status

Implemented as source-level V7 artifacts, but not qualified. V6 remains the
integrated Zmmul-only product and V8 remains a separate Zmmul+Zicsr product.
The currently deployed `bin/release/x86_64-unknown-linux-gnu/simple` reports
itself as a Rust bootstrap seed; any result from it is development-only
evidence, never V7 qualification.

## Decision

V7 is a new flattened product for exactly `rv32im` and `rv64im`. It replaces
V6's `riscv_scalar_runtime_mul_low_provider.spl` with one direct tag-2
`runtime_m_provider`. That owner implements all M rows: MUL, MULH, MULHSU,
MULHU, DIV, DIVU, REM, REMU, and on RV64 MULW, DIVW, DIVUW, REMW, REMUW.
There must be one tag-2 request/response handshake and one held completion;
separate multiplier and divider owners are forbidden because they could each
claim the same transaction.

The implemented public closure is:

```
riscv_scalar_runtime_pipeline_v7_flat.spl
  -> riscv_scalar_runtime_class_router_v7.spl
  -> runtime_m_provider (single flattened sequential owner, tag 2)
  -> riscv_scalar_runtime_global_fault_gate_v6.spl (reused, with one M fault input)
  -> riscv_scalar_runtime_pipeline_v7_flat_to_vhdl.spl
```

The provider consumes the exact canonical decoder plan through
`riscv_scalar_runtime_div_admission.spl`; its capture-time helpers are
`riscv_scalar_runtime_div_normalizer.spl` and
`riscv_scalar_runtime_restoring_divider_datapath.spl`. They are leaves of the
one owner, not sequential entities or competing protocol owners.

## Ownership and state

The owner is a one-entry finite-state protocol owner. A legal tag-2 request is
captured only after complete admission: profile/plan receipt, row/semantic,
class/effect/memory, width/form, legal state, raw fields, original/canonical
identity, instruction length, PCs/fallthrough, lineage, and event IDs. An
accepted malformed tag-2 offer sets the sticky protocol fault and makes no
architectural completion. x0 source operands are normalized at capture and
`rd=x0` suppresses writeback only.

The owner stores the entire scalar-completion envelope and never rereads live
request inputs while busy or while completion is held. Priority is reset,
protocol-fault latch, completion consume, active operation finalization,
iteration, then request capture. `request_ready` is high only for an empty,
healthy owner. Completion fields remain stable until their single
`completion_valid && completion_ready` consume edge.

For multiply, V7 retains the fixed `2*XLEN` partial-product state and V6
high-half signedness semantics. For divide/remainder it stores operation kind,
signedness, quotient-versus-remainder, normalized magnitudes, original
dividend, signs, special-case code, quotient, remainder, divisor, and count.
RV32 uses one 32-bit restoring geometry. RV64 contains distinctly named
64-bit and 32-bit restoring graphs; `*W` operations use the 32-bit graph and
sign-extend the selected 32-bit quotient/remainder exactly once to XLEN.

DIV/REM terminal counting is `count == operand_width`, unlike multiplication's
`width - 1` convention. Architectural special cases are completion results,
not traps: divisor zero produces quotient all ones or original dividend
remainder; signed minimum divided by minus one produces minimum quotient or
zero remainder.

## Product separation

V7 accepts IM only and rejects Zmmul-only, Zicsr, and combined CSR profiles.
V8's class-6/tag-3 CSR owner is not copied into V7. A later combined IM+Zicsr
product must compose this single M owner with the separate CSR owner; it may
not reintroduce a second tag-2 provider.

## Requirements and qualification

V7 source and structural tests cover REQ-G2-012 and REQ-G2-013, and the
system structural scenario compares repeated strict lowering for NFR-G2-003.
They prove source/topology only: exact IM closure, one tag-2 owner, bindings,
and deterministic emitted text. They do not prove simulated arithmetic or an
admitted compiler run.

The current provider-level clocked scenario is
`test/02_integration/compiler/riscv_scalar_runtime_m_provider_ghdl_spec.spl`.
It contains reset, backpressure, consume, fault, RV32 DIV/REM, and RV64
multiply/divide/remainder/W vectors. It does not exercise RV32 multiply
vectors and it is not a full V7-pipeline GHDL scenario.

Qualification is BLOCKED until an admitted pure-Simple self-hosted runtime is
deployed at `bin/release/x86_64-unknown-linux-gnu/simple`. `ghdl` is currently
callable, but no admitted V7 GHDL execution has been retained. `bin/simple` or
a binary identifying as the Rust bootstrap seed is not an admitted qualifier.
Before a PASS claim, add and run once an admitted full-pipeline clocked VHDL
scenario covering every M row (including RV32 multiply), and retain the
required formal/RVFI readiness evidence for the generated RTL lane.
