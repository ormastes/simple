# Strict Real-MIR to HWIR Extraction

**Executable companion:** `test/01_unit/compiler/50.mir/hwir_mir_function_extract_spec.spl`

## Purpose and scope

This focused source-level unit specification drives representative and negative
real MIR function graphs through the strict HWIR extractor. It covers closed
Zca intrinsic admission, concrete RV32/RV64 boundaries, typed local/control
flow validation, source-origin propagation, selected fixed-width data paths,
and strict module routing without a legacy fallback.

## Scenarios

1. Extract declared compressed semantic rows, predecode fixtures, constants,
   operations, joins, and selected RV32/RV64-specific variants.
2. Inspect typed port widths, origins, strict route markers, and selected VHDL
   text from extracted fixtures.
3. Reject unsupported profile/intrinsic forms, malformed signatures, invalid
   MIR control/data flow, non-hardware and clocked functions, and unsupported
   modules before a legacy route can be selected.

## Requirement traceability

- REQ-G2-003 — strict HWIR lowering admits only the explicitly supported real
  MIR input boundary and rejects unsupported forms without legacy fallback.

## Evidence boundary

This is extractor/source-shape evidence. It does not execute an instruction
stream, establish full Zca coverage, prove sequential HWIR, run generated RTL
in GHDL, compare against Sail, run riscv-formal/SBY, or qualify a synthesized
or deployed RISC-V artifact.
