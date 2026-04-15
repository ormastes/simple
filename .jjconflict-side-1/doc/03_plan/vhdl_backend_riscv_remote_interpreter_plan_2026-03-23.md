# VHDL Backend + RISC-V Simple Hardware + Simulated Remote Interpreter Plan

**Date:** 2026-03-23
**Status:** In Progress
**Scope:** Complete the VHDL backend enough to generate real hardware from Simple, migrate the FPGA RISC-V example to Simple source, and run the embedded remote interpreter test runner on a simulated RV32 CPU
**Strategy:** Simple-first, hardware-subset-specific, fail-fast on unsupported constructs

**Current repo state (2026-03-31):**
- Phase 1 is now substantially complete in the current tree:
  - `src/compiler/70.backend/backend/vhdl_backend.spl` now hard-fails unsupported MIR/type/constant paths instead of emitting silent placeholder comments.
  - `compile_package()` and `compile_process()` are implemented against live MIR-backed code paths.
  - focused backend specs cover package emission, process emission, supported MIR lowering, and fail-fast behavior.
- The remote baremetal composite runner now recognizes the GHDL RV32 remote shape used in this repo:
  - `interpreter(remote(baremetal(ghdl(riscv32))))`
  - composite execution can route checked-in ELF artifacts through the semihosted GHDL runner.
- Verification is strong for the implemented slice:
  - targeted unit, system, feature, and integration suites pass
  - `bin/simple build lint` passes for the current tree, with existing repo-wide warnings still present outside this plan slice
- The larger end-to-end goal is still not complete:
  - the mailbox-based simulated remote interpreter lane is not implemented
  - the RV32 hardware example is still handwritten RTL rather than Simple-defined hardware
  - `tb_remote.vhd` image-loading and real transport wiring remain incomplete

**Blocking milestone note (2026-04-02):**
- the current runtime blocker for the broader RISC-V program is true RV64 user-mode exec, documented separately in:
  - `doc/01_research/local/rv64_user_mode_exec.md`
  - `doc/01_research/domain/rv64_user_mode_exec.md`
  - `doc/02_requirements/feature/rv64_user_mode_exec.md`
  - `doc/03_plan/rv64_user_mode_exec.md`
- this VHDL/remote-interpreter plan should now be read as a downstream program document, not the current blocker plan

---

## Executive Summary

This plan covers three linked goals:

1. Make the VHDL backend a real compiler backend rather than a partial text emitter.
2. Move the `examples/09_embedded/fpga_riscv/` CPU example from handwritten VHDL to Simple-defined hardware source compiled through the VHDL backend.
3. Add a simulation-backed remote baremetal lane so `simple test` can execute an embedded remote interpreter on the simulated RV32 CPU.

Current repo state still does not satisfy all of those goals end to end:

- `src/compiler/70.backend/backend/vhdl_backend.spl` no longer relies on the old unsupported-instruction comment fallbacks for the implemented MIR subset, but the backend is still not a complete end-to-end hardware flow.
- `examples/09_embedded/vhdl/builder/*.spl` are builder demos, not normal Simple programs lowered through the backend.
- `examples/09_embedded/fpga_riscv/rtl/*.vhd` is handwritten VHDL today.
- `examples/09_embedded/fpga_riscv/test/run_test.sh` proves an assembly-to-simulation smoke path only.
- `examples/09_embedded/fpga_riscv/rtl/tb_remote.vhd` elaborates, but its hex-loading path is unfinished and it is not wired to the remote interpreter runtime or `simple test`.

The required design decision is explicit:

- The VHDL backend must target a restricted hardware-oriented Simple subset.
- It must not attempt to lower arbitrary application Simple into hardware.
- The remote interpreter transport for the simulation lane must use a stable mailbox/protocol contract, not ad hoc LED-only checks.

---

## Current State

### What Works Now

- `examples/09_embedded/fpga_riscv/test/run_test.sh` can assemble a RISC-V assembly test, generate a VHDL package, run GHDL, and check the LED result.
- `examples/09_embedded/fpga_riscv/rtl/tb_remote.vhd` analyzes and elaborates with GHDL.
- Existing remote baremetal documentation and specs already define the user-facing mode shape for remote lanes:
  - `doc/06_spec/tooling/simple_test.md`
  - `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
  - `test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl`

### What Is Incomplete

- `bin/simple compile --backend=vhdl ...` is not healthy enough for reliable end-to-end verification in the current workspace.
- `src/compiler/70.backend/backend/vhdl_backend.spl` still emits comments for unsupported MIR instructions instead of hard errors.
- `compile_package()` and `compile_process()` in the VHDL backend trait implementation are now implemented, but broader subset validation and backend CLI integration still need more proof.
- The VHDL examples under `examples/09_embedded/vhdl/` validate the builder API, not the backend.
- The FPGA RISC-V design is not sourced from Simple code.
- `tb_remote.vhd` has a partial `load_hex()` implementation and currently documents that real loading is not done there.
- The `simple test` remote baremetal lane is currently QEMU/GDB oriented, not VHDL/GHDL simulation oriented.

### Observed Gaps To Preserve In Planning

- Path/docs drift exists in this area and must be cleaned up as part of the implementation.
- The current handwritten RTL is valuable as a temporary golden reference and migration oracle.
- The simulated lane should avoid depending on TRACE32/OpenOCD host state.

---

## Target End State

### User Story A: Real VHDL Backend

A developer can write restricted hardware-oriented Simple code and run:

```bash
bin/simple compile --backend=vhdl -o out.vhd path/to/module.spl
```

and get:

- deterministic synthesizable VHDL-2008 output
- hard errors for unsupported constructs
- GHDL-analyzable output

### User Story B: Simple-Defined RV32 Hardware Example

The files under `examples/09_embedded/fpga_riscv/` are primarily generated from Simple hardware sources, not maintained as handwritten RTL.

### User Story C: Embedded Remote Interpreter On Simulated RV32 CPU

A developer can run a real test lane through the standard test entrypoint, for example:

```bash
bin/simple test test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl \
  '--mode=interpreter(remote(baremetal(riscv32_sim_vhdl)))'
```

and the runner will:

- build the remote target payload
- generate/load the instruction image into the simulated CPU
- run the simulated RV32 CPU under GHDL
- communicate with the embedded remote interpreter over a mailbox transport
- parse machine-readable test results
- return normal pass/fail status

---

## Architectural Decisions

### 1. Restrict The VHDL Backend To A Hardware Subset

The backend must target an explicit hardware-only subset with these initial properties:

- fixed-width integers and booleans
- static arrays and records
- ports, signals, constants
- combinational logic
- clocked logic
- fixed memory blocks / ROM / RAM descriptions
- bounded loops only
- no heap allocation
- no GC
- no async runtime
- no dynamic dispatch
- no host FFI

This subset should be enforced by validation before VHDL text generation.

### 2. Separate Hardware DSL Concerns From General Simple

General application Simple and hardware-description Simple must not be conflated.
The recommended approach is:

- retain general AST/MIR infrastructure where possible
- add hardware-oriented annotations/types/builders/subset rules
- reject unsupported software constructs explicitly

### 3. Use A Mailbox Transport For Simulation Remote Execution

The simulated remote interpreter lane should use memory-mapped or dual-port-RAM mailboxes, not semihosting and not LED-only signaling.

Minimum mailbox design:

- host-to-target command area
- target-to-host response area
- status register
- ready register
- error register
- monotonically increasing sequence or generation counter

### 4. Keep Handwritten RTL As Temporary Reference Only

During migration, the current files in `examples/09_embedded/fpga_riscv/rtl/` remain:

- migration oracle
- simulation baseline
- structural equivalence reference

They are not the long-term source of truth.

---

## Proposed Architecture

```text
Simple Hardware Source
    ↓
Hardware Subset Validation
    ↓
MIR (restricted / annotated)
    ↓
VHDL Backend
    ↓
Generated RTL + package files
    ↓
GHDL analysis/elaboration/simulation
    ↓
RV32 CPU + mailbox transport
    ↓
Embedded remote interpreter payload
    ↓
simple test remote-baremetal adapter
```

### Main Layers

#### Layer 1: Hardware Source Layer

New or adapted Simple modules that describe:

- ALU
- register file
- decoder
- PC/update logic
- MMIO/register blocks
- ROM/RAM layout

#### Layer 2: Validation Layer

Reject unsupported language/MIR patterns before emission.

Expected outputs:

- structured backend errors
- capability reports
- deterministic failure categories

#### Layer 3: VHDL Codegen Layer

Produce:

- package declarations
- entity declarations
- architecture bodies
- process bodies
- instances and port maps
- ROM/RAM init artifacts where needed

#### Layer 4: Simulation Host Shim

`tb_remote.vhd` or a replacement testbench must:

- instantiate the generated SoC/core
- load the instruction image
- expose the transport mailbox
- emit a stable host-readable transcript

#### Layer 5: `simple test` Integration

Extend the remote baremetal test runner to launch the GHDL-based target and parse remote test output.

---

## Implementation Phases

## Phase 1: Make VHDL Backend Fail Correctly

**Goal:** Remove silent partial behavior and establish a strict supported subset.
**Blocking:** None
**Estimated Outcome:** backend either generates valid VHDL for supported inputs or fails explicitly

### Tasks

- [x] Audit all catch-all and comment-emission paths in `src/compiler/70.backend/backend/vhdl_backend.spl`
- [x] Replace comment-based unsupported emission with structured `CompileError`
- [x] Implement the currently stubbed trait methods:
  - `compile_package()`
  - `compile_process()`
- [x] Define and enforce an initial supported MIR instruction subset through explicit backend failures
- [ ] Add a hardware-subset verifier pass before VHDL emission
- [ ] Make unsupported software/runtime constructs fail during validation, not after emission
- [x] Add focused tests for supported VHDL MIR patterns and fail-fast cases

### Files

- `src/compiler/70.backend/backend/vhdl_backend.spl`
- `src/compiler/70.backend/backend/vhdl/vhdl_builder.spl`
- `src/compiler/70.backend/vhdl_constraints.spl`
- new validator module under `src/compiler/70.backend/backend/`
- test files under `test/unit/compiler/backend/`

### Exit Criteria

- `--backend=vhdl` never succeeds by emitting partial nonsense with “Unsupported instruction” comments
- every unsupported path returns a clear error
- supported examples produce GHDL-valid output

### 2026-03-31 Implementation Note

This phase is functionally complete for the current backend slice, but not fully closed from a product perspective because the repo still lacks:

- a pre-emission hardware-subset validator
- a backend CLI smoke path that proves `bin/simple compile --backend=vhdl`
- a generated RTL example that replaces builder-only proof

---

## Phase 2: Convert VHDL Examples Into Real Backend Coverage

**Goal:** Stop treating builder demos as backend proof.
**Blocking:** Phase 1

### Tasks

- [x] Reclassify `examples/09_embedded/vhdl/builder/*.spl` as builder/API demos
- [ ] Add backend-driven VHDL examples written as normal restricted Simple source
- [ ] Add golden VHDL outputs for backend-generated examples
- [ ] Run `ghdl -a` in tests for generated outputs
- [ ] Add CLI smoke specs for `simple compile --backend=vhdl`

### Files

- `examples/09_embedded/vhdl/`
- `test/feature/usage/vhdl_spec.spl`
- new backend-integration specs under `test/integration/` or `test/feature/usage/`

### Exit Criteria

- the repo has at least one example that proves the compiler backend path, not just the builder path

---

## Phase 3: Introduce A Hardware-Oriented Simple Source Model

**Goal:** Create the source-side model that the VHDL backend can compile reliably.
**Blocking:** Phase 1

### Tasks

- [ ] Define the source syntax/API for hardware modules, ports, signals, clock domains, and bounded loops
- [ ] Add type rules for fixed-width hardware integers and vectors
- [ ] Decide how to model:
  - combinational processes
  - clocked processes
  - reset behavior
  - ROM/RAM declarations
  - port maps
- [ ] Add lowering rules from the hardware source layer into MIR/VHDL-specific MIR operations
- [ ] Document the allowed subset and invalid patterns

### Design Constraint

This phase must avoid turning the entire language into a hardware DSL. The goal is a clear, narrow, explicit subset.

### Exit Criteria

- a developer can author hardware-oriented Simple source without dropping down into direct `VhdlBuilder` text calls

---

## Phase 4: Migrate The RV32 Hardware Example To Simple

**Goal:** Make `examples/09_embedded/fpga_riscv/` sourced from Simple hardware modules.
**Blocking:** Phases 1-3

### Tasks

- [ ] Create Simple hardware source modules for:
  - ALU
  - register file
  - decoder
  - core datapath
  - top-level wrapper
- [ ] Generate VHDL for each module through the backend
- [ ] Compare generated RTL against the current handwritten RTL for behavior and interface parity
- [ ] Preserve or regenerate:
  - `constraints/zedboard.xdc`
  - `build.tcl`
  - `program.tcl`
- [ ] Add a Simple build/regeneration script for the example
- [ ] Keep handwritten VHDL only as migration reference until parity is established

### Suggested Source Layout

- `examples/09_embedded/fpga_riscv/simple_hw/alu.spl`
- `examples/09_embedded/fpga_riscv/simple_hw/regfile.spl`
- `examples/09_embedded/fpga_riscv/simple_hw/decoder.spl`
- `examples/09_embedded/fpga_riscv/simple_hw/rv32i_core.spl`
- `examples/09_embedded/fpga_riscv/simple_hw/zedboard_top.spl`
- `examples/09_embedded/fpga_riscv/build_rtl.spl`

### Exit Criteria

- the checked-in example can be regenerated from Simple source
- GHDL analysis succeeds on generated files
- the existing assembly smoke tests still pass

---

## Phase 5: Add Proper Program Image Loading For Simulation

**Goal:** Replace ad hoc and partial image-loading behavior with a real pipeline.
**Blocking:** Phase 4 for final wiring, but can start earlier

### Current Problem

`examples/09_embedded/fpga_riscv/rtl/tb_remote.vhd` contains a partial `load_hex()` path and currently does not provide a complete host-driven image-loading contract.

### Tasks

- [ ] Define one canonical instruction-image format for the simulation lane
- [ ] Add a host-side generator from Simple remote-target output to that format
- [ ] Support one of:
  - generated VHDL package constants
  - generated memory init file consumed by testbench
  - generated ROM component/entity
- [ ] Remove dead or misleading partial loaders
- [ ] Make image generation part of the remote-interpreter simulation flow, not a manual side script

### Exit Criteria

- the simulated CPU loads the test/remote payload from a deterministic compiler-driven artifact

---

## Phase 6: Implement The Simulation Mailbox Transport

**Goal:** Provide a real host-target protocol for the simulated remote interpreter.
**Blocking:** Phase 5

### Mailbox Contract

Minimum fields:

- `command_ready`
- `command_opcode`
- `command_arg0`
- `command_arg1`
- `command_length`
- `response_ready`
- `response_status`
- `response_length`
- payload buffer
- sequence counter

### Tasks

- [ ] Define the mailbox memory map
- [ ] Implement hardware-side mailbox access logic in the generated RV32 top-level or memory subsystem
- [ ] Implement host-side mailbox driver behavior in the VHDL testbench
- [ ] Define timeout and reset behavior
- [ ] Define transcript/debug lines for failed exchanges
- [ ] Document the wire protocol in `doc/06_spec/` or `doc/05_design/`

### Exit Criteria

- host and simulated target can exchange commands and responses without semihosting

---

## Phase 7: Port The Remote Interpreter Runtime To The Simulated RV32 Lane

**Goal:** Run the actual remote interpreter over the mailbox transport.
**Blocking:** Phase 6

### Tasks

- [ ] Add a new remote target/mode string, recommended:
  - `interpreter(remote(baremetal(riscv32_sim_vhdl)))`
- [ ] Implement a target adapter for the simulated transport
- [ ] Support initial operations:
  - ping
  - memory read
  - memory write
  - run/resume
  - halt/status
  - fetch textual output
- [ ] Reuse existing remote baremetal abstractions where possible
- [ ] Keep protocol/client code shared with existing remote infrastructure when possible
- [ ] Clearly separate simulation-specific transport from QEMU semihosting and TRACE32/OpenOCD lanes

### Candidate Integration Points

- `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
- `test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl`
- shared remote client/target modules under `src/lib/.../debug/remote/` or equivalent current location

### Exit Criteria

- the simulated target answers real remote-interpreter commands

---

## Phase 8: Add Embedded Test Runner Output And Parsing

**Goal:** Make the simulated lane useful for `simple test`, not just manual inspection.
**Blocking:** Phase 7

### Tasks

- [ ] Define a machine-readable embedded test transcript format
- [ ] Implement target-side emission helpers in Simple for:
  - suite start
  - test start
  - pass
  - fail
  - summary
- [ ] Make the VHDL testbench forward transcript lines to stdout predictably
- [ ] Add host-side parser support in the standard test runner
- [ ] Map remote transcript failures to standard `simple test` failure reporting

### Design Constraint

This transcript must be stable and ASCII-safe. Do not depend on pretty terminal formatting for correctness.

### Exit Criteria

- `simple test` can consume embedded test results as first-class pass/fail events

---

## Phase 9: Integrate With `simple test`

**Goal:** Expose the simulation lane through the standard test interface.
**Blocking:** Phase 8

### Tasks

- [ ] Extend remote baremetal mode parsing to recognize `riscv32_sim_vhdl`
- [~] Add a launch adapter that:
  - [x] routes checked-in ELF artifacts through the GHDL semihost runner for `interpreter(remote(baremetal(ghdl(riscv32))))`
  - [ ] compiles the remote target payload
  - [ ] generates the instruction image
  - [ ] compiles/elaborates the testbench
  - [ ] parses a mailbox-backed remote transcript
- [x] Add host capability checks for:
  - GHDL availability
  - existing remote-baremetal host tooling already covers the QEMU lane
- [x] Add skip/blocked handling when host tools are missing
- [~] Keep runtime and docs aligned with real command lines

### Exit Criteria

- `simple test` can execute the VHDL-sim remote interpreter lane end to end

### 2026-03-31 Implementation Note

The current tree now supports a narrower proof than the original phase target:

- parser and runner support for the GHDL RV32 remote shape
- execution of checked-in ELF artifacts through the GHDL semihost runner
- system/integration coverage for the live routing path

It does not yet provide the full `riscv32_sim_vhdl` instruction-image plus mailbox-transport pipeline described in this plan.

---

## Phase 10: Documentation, Cleanup, And CI

**Goal:** Ensure this lane is discoverable, reproducible, and kept working.
**Blocking:** Phases 1-9

### Tasks

- [ ] Update `examples/09_embedded/README.md`
- [ ] Update `doc/06_spec/tooling/simple_test.md`
- [ ] Add one architecture/design doc for the VHDL sim remote lane
- [ ] Remove stale references to old paths and non-working commands
- [ ] Add CI coverage for:
  - backend-generated VHDL examples
  - GHDL analysis
  - at least one simulation smoke lane
- [ ] Keep hardware/host blockers clearly separated from repo bugs

### Exit Criteria

- docs match the real commands
- at least one automated simulation-based remote-interpreter smoke test runs in CI

---

## Detailed Task Inventory

## A. Backend Tasks

- [ ] Add VHDL subset verifier
- [ ] Remove comment-based unsupported fallbacks
- [ ] implement `compile_package()`
- [ ] implement `compile_process()`
- [ ] normalize type mapping and literal mapping for generated hardware code
- [ ] add structured codegen errors with file/context where possible
- [ ] add unit coverage for all VHDL-specific MIR instructions

## B. Example Migration Tasks

- [ ] define Simple hardware modules for ALU/regfile/decoder/core/top
- [ ] add generator/build script for example RTL
- [ ] preserve current handwritten RTL as temporary golden reference
- [ ] compare interfaces and behavior between handwritten and generated RTL
- [ ] keep ZedBoard-specific packaging files in sync

## C. Simulation Runtime Tasks

- [ ] choose canonical instruction image format
- [ ] wire generated ROM/init into simulation
- [ ] define mailbox MMIO map
- [ ] implement host-side mailbox driver in testbench
- [ ] implement target-side mailbox runtime
- [ ] define reset/timeout/error semantics

## D. Test Runner Tasks

- [ ] add `riscv32_sim_vhdl` mode
- [ ] implement launcher/orchestrator
- [ ] implement transcript parser
- [ ] add remote-interpreter smoke spec
- [ ] add embedded test suite smoke spec
- [ ] classify missing host tools as skip/blocked

## E. Documentation Tasks

- [ ] document hardware subset
- [ ] document simulation transport
- [ ] document end-to-end test command
- [ ] document migration status and remaining handwritten RTL

---

## Risks

### Risk 1: Overreaching Backend Scope

Trying to lower arbitrary Simple into hardware will stall the effort.

**Mitigation:** define and enforce the subset early.

### Risk 2: MIR Shape Not Suitable For Hardware

Current MIR may need annotation or restriction to express hardware processes cleanly.

**Mitigation:** add a dedicated validation/lowering stage rather than forcing the backend to guess intent.

### Risk 3: Transport Drift Across Lanes

QEMU semihosting, TRACE32, and VHDL simulation could diverge into unrelated protocols.

**Mitigation:** keep the remote command model shared; vary only the transport adapter.

### Risk 4: Builder Demo Confusion Persists

The repo may continue treating manual `VhdlBuilder` output as proof of backend health.

**Mitigation:** separate demo coverage from backend coverage in docs and tests.

### Risk 5: Testbench Becomes The Real Runtime

Too much logic in the VHDL testbench would hide missing target functionality.

**Mitigation:** keep the testbench as a transport shim only; the target runtime must own protocol behavior.

---

## Recommended Milestones

### Milestone 1

VHDL backend is strict and non-silent.

### Milestone 2

Backend-generated example VHDL passes GHDL analysis.

### Milestone 3

Generated Simple-defined RV32 blocks replace handwritten ALU/regfile/decoder/core.

### Milestone 4

Simulation mailbox transport works with a small command set.

### Milestone 5

Embedded remote interpreter answers commands in GHDL simulation.

### Milestone 6

`simple test` runs the simulated remote lane end to end.

---

## Definition Of Done

This work is done when all of the following are true:

- `bin/simple compile --backend=vhdl` works for the supported hardware subset.
- Unsupported constructs fail explicitly before or during codegen with clear errors.
- The example under `examples/09_embedded/fpga_riscv/` is generated from Simple source, with handwritten RTL retained only as migration reference or removed after parity.
- GHDL simulation works from compiler-generated instruction/ROM artifacts rather than ad hoc manual test setup.
- A mailbox-based host-target transport exists for the simulated RV32 CPU.
- The embedded remote interpreter runs on the simulated target and responds to real remote commands.
- `simple test '--mode=interpreter(remote(baremetal(riscv32_sim_vhdl)))' ...` executes a real simulation-backed lane and reports pass/fail.
- Repo docs and commands match the actual implementation.

---

## Suggested Immediate Next Actions

1. Fix the VHDL backend crash path and convert all unsupported-instruction fallbacks into hard errors.
2. Add one backend-generated VHDL example plus a `ghdl -a` integration spec.
3. Define the hardware subset and source model before attempting broad RV32 migration.
4. Replace the unfinished `tb_remote.vhd` hex-loader idea with a proper mailbox transport design.
5. Add the new simulation target mode to the remote baremetal planning/docs before implementation starts.
