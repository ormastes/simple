# Mixed Sequential HWIR Datapath and Explicit LSU Geometry

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl`

## Purpose and scope

This focused source-level unit specification constructs one RV32 strict
sequential HWIR module whose combinational datapath feeds guarded state. It
checks the emitted VHDL text for a typed 32-bit add, 8-bit truncation, 32-bit
sign extension, equality comparison, mux selection, and the selected value's
assignment into the state register. It also checks that explicit LSU bus and
mask geometry is validated independently of the selected core width and that
the RV32/RV64 product defaults expose their respective bus widths.

## Scenarios

1. Build the `mixed_sequential_datapath` module with explicit `clk`, `rst`,
   capture, operand, valid, and value ports; validate it; then render strict
   VHDL and inspect the typed add/truncate/sign-extension/compare/select
   assignments before the guarded `value_reg` state assignment.
2. Admit explicit 64-bit/8-byte LSU geometry, reject incompatible 64-bit/4-byte
   and 48-bit/6-byte geometry, and inspect the RV32 and RV64 product-default
   bus widths of 32 and 64 bits.
3. Add an XLEN-wide unsigned-greater-or-equal operation whose result is a
   one-bit signal and verify its typed `unsigned(lhs) >= unsigned(rhs)` VHDL.
4. Reject an unsupported operation, an output-only operand used as readable
   input, and a datapath signal with two drivers; rejected modules produce no
   successful strict-VHDL result.
5. Change a typed datapath constant and verify that the module structural hash,
   emitted graph receipt, and VHDL provenance all track the change.

## Requirement traceability

- REQ-G2-004 — a supported typed combinational module emits deterministic,
  non-empty strict VHDL while preserving its typed source lineage. This scenario
  inspects the bounded datapath and sequential assignment text.
- NFR-G2-003 — width selection is elaboration-time data. This scenario covers
  the bounded RV32 module and independently validates explicit LSU geometry
  plus the concrete RV32/RV64 default bus widths; it does not assert the full
  emitted-module no-XLEN-multiplexer condition.
- NFR-G2-011 — the first sequential Gen2 lane uses explicit typed
  state/register widths and a named synchronous reset domain. This scenario
  constructs the two typed registers and their guarded bindings, but it does
  not simulate reset or stalled-payload behavior.
- NFR-G2-001 — deterministic structural identity includes the complete typed
  datapath; a changed constant cannot retain the prior graph receipt.

## Evidence boundary

This is source-level typed-HWIR construction, validation, and strict-VHDL-text
evidence for one synthetic mixed sequential datapath and LSU configuration
geometry. It does not execute generated VHDL or RTL, simulate arithmetic,
clock, reset, capture, or guard behavior, issue an LSU transaction, prove LSU
protocol or memory semantics, establish complete RV32/RV64 datapath coverage,
run GHDL/Sail/riscv-formal/SBY, synthesize hardware, or qualify a generated or
deployed hardware artifact.
