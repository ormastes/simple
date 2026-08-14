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

## Preconditions

- Use a provenance-admitted self-hosted Simple CLI; the Rust seed and the
  currently crashing deployed binary are diagnostic only.
- Run from the repository root with compiler sources available under
  `src/compiler`.
- Install GHDL with VHDL-2008 support before attempting the still-open target
  behavior scenario.

## Operator workflow

1. Run the executable companion once in interpreter mode.
2. Run `sspec-maintain scan` once and inspect all seven scores, blockers,
   mirror state, and requirement traceability.
3. Regenerate this manual with `spipe-docgen --output doc/06_spec --no-index`
   and require `0 stubs`.
4. Run the planned GHDL analyze/elaborate/simulate scenario and retain its VHDL
   and logs before promoting target behavior.

## Scenarios

1. Build the `mixed_sequential_datapath` module with explicit `clk`, `rst`,
   capture, operand, valid, and value ports; validate it; then render strict
   VHDL and inspect the typed add/truncate/sign-extension/compare/select
   assignments before the guarded `value_reg` state assignment.
   The same module declares an exact-width bit-vector constant and emits one
   fixed bit extract and one fixed slice; the datapath assignment must precede
   the clocked process.
2. Admit explicit 64-bit/8-byte LSU geometry, reject incompatible 64-bit/4-byte
   and 48-bit/6-byte geometry, and inspect the RV32 and RV64 product-default
   bus widths of 32 and 64 bits.
3. Add an XLEN-wide unsigned-greater-or-equal operation whose result is a
   one-bit signal and verify its typed `unsigned(lhs) >= unsigned(rhs)` VHDL.
4. Reject an unsupported operation, an output-only operand used as readable
   input, a register used as an operation destination, an invalid resize
   direction, and a datapath signal with two drivers; rejected modules produce
   no successful strict-VHDL result.
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
- REQ-G2-004 / NFR-G2-001/003/011 — typed combinational values are owned and
  validated by the sequential module, render before the clocked process, have
  one signal driver, preserve resize direction, and keep LSU transport geometry
  explicit.

## Evidence boundary

This is source-level typed-HWIR construction, validation, and strict-VHDL-text
evidence for one synthetic mixed sequential datapath and LSU configuration
geometry. It does not execute generated VHDL or RTL, simulate arithmetic,
clock, reset, capture, or guard behavior, issue an LSU transaction, prove LSU
protocol or memory semantics, establish complete RV32/RV64 datapath coverage,
run GHDL/Sail/riscv-formal/SBY, synthesize hardware, or qualify a generated or
deployed hardware artifact.

## Compatibility and limitations

The implemented source contract supports the strict emitter's bounded
operation subset and one synchronous default clock/reset domain. Parcel/trap
products still use their typed plan-only renderer and are not yet migrated to
this mixed module boundary. This manual is maintained source documentation
until the admitted self-hosted docgen command can regenerate it; it is not a
qualification receipt.

## SPipe maintenance scorecard

Status: blocked. The current self-hosted runtime fails its ABI probe and exits
139 during focused execution, so no honest seven-component scorecard or
`0 stubs` regeneration result exists for this revision. Resume commands and
the blocker record are linked from the canonical A13 plan.

## Findings and remediation

- Fixed: operation results are restricted to declared datapath signals.
- Fixed: extension and truncation directions are width-validated.
- Fixed: bit-vector constants, bit extracts, fixed slices, and render ordering
  have explicit source-level assertions.
- Open: admitted self-hosted execution, generated-manual provenance, measured
  branch coverage, and behavioral GHDL cycles.

## Generation provenance

Executable source:
`test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl`.
Canonical generator command:
`bin/simple spipe-docgen test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl --output doc/06_spec --no-index`.
No generated-pass claim is made while that command is blocked.

<details>
<summary>Executable specification</summary>

The complete executable source remains canonical at the path above. SPipe
docgen must replace this maintained link with its folded source rendering when
the admitted self-hosted CLI is restored.

</details>
