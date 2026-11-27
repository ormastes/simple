# Pure Simple VHDL RISC-V Gap Implementation Plan

> Status: COMPLETE — spipe 16/16 done

**Status:** Ready for parallel agent implementation
**Goal:** Close the minimum pure-Simple VHDL backend gaps needed before a
maintainable RV32I-class CPU can be generated from Simple source.
**Rule:** Pure Simple compiler paths own acceptance. Facade/string lowering may
remain as compatibility scaffolding, but parity claims only move when typed
AST/HIR/MIR-to-VHDL tests pass.

## Current Baseline

Pure Simple VHDL can demonstrate small hardware blocks, labeled multi-output
facade generation, basic fixed-width facade expressions, and GHDL smoke on
small examples. It is not enough for RISC-V because the typed backend still
lacks memory inference, real hardware-call composition, complete fixed-width
bit semantics, decode-friendly `match` lowering, composite ports, and
simulation/testbench support.

## Agent Assignments

<!-- rtl_riscv_mdsoc_reorg capsule mapping (AC-4, doc/05_design/app/riscv/rtl_riscv_mdsoc_capsules.md):
     Agent 1 primary capsule: vhdl.emit.metadata; Agent 2: vhdl.emit.control;
     Agent 3: vhdl.emit.data; Agent 4: vhdl.emit.control; Agent 5:
     vhdl.emit.data (secondary vhdl.emit.state); Agent 6: vhdl.emit.state;
     Agent 7: vhdl.emit.data; Agent 8: vhdl.emit.metadata. Labels are
     advisory only -- no task reassignment. -->

### Agent 1: Typed Hardware Metadata and Return Labels

<!-- capsule: vhdl.emit.metadata (secondary: vhdl.emit.control) -->

Owns parser, HIR, MIR metadata propagation.

- Preserve labeled tuple return field names in typed IR, not only facade text.
- Preserve `@hardware`, `@generic`, and `@clocked` through AST/HIR/MIR.
- Reject duplicate/sanitized output labels before backend emission.
- Add tests that prove MIR contains return labels for `sum`, `cout`,
  instruction decode fields, and bus response fields.

Acceptance:
- `pure_simple_vhdl_source_of_truth_spec.spl` metadata cases become runnable.
- Same-type labeled returns compile; same-type anonymous returns fail.

### Agent 2: Hardware Call Lowering and Virtual Aggregates

<!-- capsule: vhdl.emit.control (secondary: vhdl.emit.data) -->

Owns MIR-to-VHDL direct hardware call composition.

- Lower direct calls to `@hardware` functions into entity instances.
- Emit deterministic instance names and named `port map` connections.
- Allocate temp signals for every returned output port.
- Resolve `result.field` and numeric `result.N` from virtual aggregate temps.
- Reject indirect calls, dynamic tuple access, recursion, and unsupported calls.

Acceptance:
- `full_add` plus `add2` generated from typed IR passes GHDL analyze,
  elaborate, and synth.

### Agent 3: Fixed-Width Bit Semantics for RV32I

<!-- capsule: vhdl.emit.data (secondary: vhdl.emit.control) -->

Owns typed bit operations.

- Support `u1/u2/u3/u5/u7/u12/u20/u32/u64` values through lowering.
- Implement typed slices, concat, shifts, masks, comparisons, sign extension,
  zero extension, and truncation.
- Add diagnostics for width mismatch, signedness ambiguity, and out-of-range
  slices.
- Add instruction-field fixtures: opcode, rd, funct3, rs1, rs2, funct7,
  I/S/B/U/J immediates.

Acceptance:
- A pure Simple RV32I decode function emits synthesizable VHDL without facade
  parsing.

### Agent 4: Decode and Control Lowering

<!-- capsule: vhdl.emit.control -->

Owns `match`/case and enum-like control representation.

- Lower constant `match`/case trees to synthesizable VHDL `case` or priority
  muxes.
- Define a minimal enum encoding policy for internal control signals.
- Support ALU op, branch kind, memory op, CSR/trap state encodings.
- Reject payload enums until payload encoding is specified.

Acceptance:
- Opcode decode and ALU-control fixtures pass GHDL analyze/elaborate/synth.

### Agent 5: Register File, ROM, and RAM Inference

<!-- capsule: vhdl.emit.data (secondary: vhdl.emit.state) -->

Owns array/indexed storage and memory templates.

- Infer combinational ROM from constant arrays.
- Infer synchronous RAM from indexed mutable storage patterns.
- Implement register-file template with two read ports and one write port.
- Enforce synthesizable indexing rules and diagnostics for dynamic unsupported
  forms.

Acceptance:
- 32x32 register file fixture passes GHDL synth.
- Boot ROM fixture emits stable VHDL and passes GHDL analyze/elaborate.

### Agent 6: Clock Domains, Reset, and Sequential State

<!-- capsule: vhdl.emit.state (secondary: vhdl.emit.control) -->

Owns process/domain correctness.

- Lower clocked registers from typed IR, not facade strings.
- Support no-reset, sync reset, async reset, active-high, and active-low.
- Track domain names for PC, register file, CSR, and memory state.
- Reject implicit cross-domain reads with source and destination domain names.

Acceptance:
- PC update, pipeline register, and CSR state fixtures pass GHDL synth.

### Agent 7: Composite Ports and Bus Bundles

<!-- capsule: vhdl.emit.data (secondary: vhdl.emit.control) -->

Owns structured external interfaces.

- Flatten typed structs/tuples for VHDL ports with deterministic names.
- Support memory bus request/response bundles.
- Add collision diagnostics across flattened input/output names.
- Keep generated port order stable.

Acceptance:
- Instruction/data memory bundle fixtures emit stable, synthesizable VHDL.

### Agent 8: Simulation, Testbench, and Source Maps

<!-- capsule: vhdl.emit.metadata (secondary: vhdl.emit.control) -->

Owns verification artifacts.

- Generate minimal VHDL testbenches from Simple fixtures.
- Add source-map records from Simple spans to VHDL lines.
- Ensure failed lowering does not leave stale VHDL files.
- Add RV32I smoke programs: add/sub, load/store, branch, jump, trap-lite.

Acceptance:
- GHDL simulation executes at least one RV32I smoke program to expected
  register/memory state.

## Sequencing

1. Agent 1 must land before Agents 2, 6, and 7 can remove facade parsing.
2. Agent 3 can proceed in parallel with Agent 1 using typed width fixtures.
3. Agents 4 and 5 depend on Agent 3 for instruction fields and indexes.
4. Agent 8 starts with skipped specs, then enables simulations as Agents 2-7
   land.

## Required Checks

```sh
bin/simple test --no-cache test/03_system/compiler/pure_simple_vhdl_source_of_truth_spec.spl
bin/simple test --no-cache test/03_system/compiler/vhdl_source_facade_spec.spl
bin/simple test --only-skipped --list-skip-features --pending test/01_unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
sh scripts/check/check-core-runtime-smoke.shs bin/simple
SIMPLE_BINARY=bin/simple sh scripts/check/check-mcp-native-smoke.shs
```

## Done Definition

The RISC-V gap is closed when a pure Simple RV32I single-cycle core can be
compiled to VHDL from typed compiler IR, passes GHDL analyze/elaborate/synth,
and runs at least one generated testbench without relying on facade string
parsing for hardware calls, bit slices, memories, decode, or ports.
