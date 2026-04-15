# VHDL Backend Completion Plan

**Date:** 2026-04-04  
**Status:** Complete  
**Scope:** Complete the VHDL backend so it moves from an experimental backend with a real codegen slice to a supported hardware-oriented backend with explicit subset boundaries and authoritative proof.

## 1. Current Classification

The VHDL backend is **experimental**, not partial.

Why it is experimental:
- a real backend surface exists
- MIR-to-VHDL generation exists
- strict fail-fast behavior exists for some unsupported paths
- GHDL-related proof lanes exist around surrounding simulation flows

Why it is not yet merely “partial but supported”:
- the supported hardware subset is not yet published as a stable backend contract
- end-to-end CLI/backend-generated hardware proof is still incomplete
- simulation/synthesis proof is uneven
- example and backend boundaries are still mixed between builder demos and true backend outputs

## 2. Completion Target

The feature is complete when the repo can truthfully state:

> The VHDL backend compiles a documented hardware-oriented Simple subset to synthesizable VHDL-2008, validates generated designs through GHDL analysis, and supports an authoritative simulation-backed proof path for supported targets.

This does **not** require universal language-to-hardware compilation.

It **does** require:
- a strict documented supported subset
- deterministic backend CLI behavior
- valid emitted VHDL for the supported subset
- GHDL analysis/elaboration proof for generated output
- a simulation-backed proof lane for at least one reference target

## 3. Current Gaps

### 3.1 The supported language-to-hardware subset is not fully closed

Current issue:
- the backend has a real codegen slice, but not a completed, published subset contract for what Simple constructs are legal for VHDL lowering

Completion requirement:
- define the exact supported subset for:
  - types
  - constants
  - functions/processes
  - control flow
  - stateful versus combinational logic

### 3.2 Backend CLI proof is still weak

Current issue:
- the repo already notes that `bin/simple compile --backend=vhdl` is not yet healthy enough as a reliable end-to-end verification path

Completion requirement:
- `simple compile --backend=vhdl` must be authoritative for the supported subset
- failures must be hard errors, never partial nonsense output

### 3.3 Builder demos and backend-generated designs are still conflated

Current issue:
- examples under `examples/09_embedded/vhdl/` include builder/API demos rather than only backend-generated designs

Completion requirement:
- clearly separate:
  - backend-generated examples
  - builder API demos
  - simulation fixtures

### 3.4 GHDL proof is not yet the canonical backend proof for generated VHDL

Current issue:
- GHDL exists in the broader remote/simulation ecosystem
- but the backend still lacks a closed loop where generated VHDL is analyzed and elaborated as the normal proof path

Completion requirement:
- add GHDL `-a` and `-e` as authoritative backend proof for supported outputs

### 3.5 The simulation-backed CPU flow is incomplete

Current issue:
- the repo has a GHDL RV32 simulation path and a plan for `riscv32_sim_vhdl`
- but the backend-generated hardware lane is not yet the finished source of truth for that path

Completion requirement:
- finish one simulation-backed hardware target lane using backend-generated VHDL or explicitly keep it out of the backend completion milestone

## 4. Final Backend Model

### 4.1 Restricted hardware-oriented Simple subset

The VHDL backend must be framed as a compile target for a restricted subset, not arbitrary general-purpose Simple.

Required first-class subset categories:
- integer-like scalar types with defined mapping
- booleans, bits, enums, records
- constants and packages
- signals/ports
- combinational processes
- clocked/register processes

Explicitly deferred unless proven:
- unrestricted heap/dynamic allocation
- general polymorphism without hardware lowering rules
- open-ended runtime features
- arbitrary side-effecting host semantics

### 4.2 Strict fail-fast backend

The VHDL backend must never emit partial or misleading hardware for unsupported MIR.

Required behavior:
- unsupported construct -> hard compile error
- no silent placeholder comments as a success path

### 4.3 GHDL as the reference validation tool

Use GHDL analysis/elaboration as the first authoritative correctness gate for generated VHDL.

Why:
- it is already part of the repo’s simulation story
- it provides a practical compiler-level validation loop
- it is sufficient to close the backend on correctness before broader synthesis closure

### 4.4 Simulation-backed proof as the next milestone

After emitted VHDL is valid, the next closure step is simulation-backed execution for one reference target.

Recommended first target:
- RV32 simulation lane via GHDL

## 5. Implementation Phases

### Phase 1. Freeze the supported VHDL subset

Goal:
- remove ambiguity about what `--backend=vhdl` is supposed to accept

Tasks:
- publish the supported subset for:
  - MIR instructions
  - types
  - constants
  - package constructs
  - process forms
- define unsupported constructs explicitly

Exit criteria:
- one concise subset contract exists in docs and tests

### Phase 2. Finish strict subset validation

Goal:
- reject unsupported hardware constructs before emission

Tasks:
- tighten `vhdl_constraints` checking
- validate unsupported MIR/type/constant paths early
- ensure emitted errors are actionable and stable

Required diagnostics:
- unsupported instruction
- unsupported type mapping
- unsupported control/data dependency shape
- unsupported side effect or runtime feature

Exit criteria:
- invalid source fails before or during lowering with deterministic diagnostics

### Phase 3. Close package/entity/process emission for the supported subset

Goal:
- make the codegen slice complete for the published subset

Tasks:
- finish type mapping for the supported scalar/enum/record subset
- finish entity/architecture emission
- finish package emission
- finish process generation for combinational and clocked paths

Required proof:
- generated VHDL contains no fallback placeholder text for supported input

Exit criteria:
- all supported subset examples emit structurally valid VHDL

### Phase 4. Make the CLI path authoritative

Goal:
- make `simple compile --backend=vhdl` the supported entrypoint

Tasks:
- fix CLI/backend integration so backend emission succeeds for the supported subset
- ensure output file behavior is deterministic
- ensure compile failures propagate correctly

Required tests:
- CLI smoke spec for `simple compile --backend=vhdl`
- output-file creation and non-empty content
- unsupported input fails with explicit error

Exit criteria:
- CLI success/failure behavior is stable and tested

### Phase 5. Add GHDL analysis/elaboration as the backend validation gate

Goal:
- prove generated VHDL is accepted by a real VHDL toolchain

Tasks:
- add integration specs that run:
  - `ghdl -a --std=08`
  - `ghdl -e --std=08`
- ensure generated packages/entities elaborate correctly for supported examples

Required tests:
- generated simple counter/register design
- generated package + entity pair
- one negative spec where invalid design is rejected

Exit criteria:
- backend-generated VHDL passes GHDL analysis/elaboration on the supported subset

### Phase 6. Separate demos from authoritative backend examples

Goal:
- keep proof evidence clean

Tasks:
- reclassify `examples/09_embedded/vhdl/` into:
  - backend-generated examples
  - builder/API demos
  - simulation fixtures
- ensure README/docs do not present builder demos as proof of backend lowering

Exit criteria:
- example directories clearly distinguish proof-bearing backend outputs from helper APIs

### Phase 7. Choose the simulation-backed completion milestone

Goal:
- define what “complete enough” means beyond syntactic VHDL validity

Two acceptable milestone options:

1. **Backend-complete, simulation-light**
- generated VHDL is GHDL-valid
- simulation-backed CPU flow remains a follow-on milestone

2. **Backend-complete with one simulation target**
- generated VHDL participates in a real simulation-backed lane
- preferred lane: RV32 simulated target

Recommended:
- finish one simulation-backed lane so the backend has one true execution proof, not only syntax validity

Exit criteria:
- one generated-hardware simulation lane is authoritative, or the scope is explicitly capped at validated code generation

### Phase 8. Finish or quarantine the `riscv32_sim_vhdl` lane

Goal:
- remove ambiguity around the planned simulation-backed interpreter/remote lane

Tasks:
- either implement:
  - target spelling
  - image/materialization pipeline
  - mailbox/result transport
  - simulation-backed pass/fail reporting
- or explicitly quarantine it outside the VHDL completion milestone

Exit criteria:
- no half-supported “planned target” remains in an ambiguous state

### Phase 9. Publish the VHDL support matrix

Goal:
- make support claims auditable

Required matrix fields:
- supported subset category
- emission status
- GHDL analysis status
- elaboration status
- simulation status
- synthesis status

Classify each as:
- stable
- supported
- partial
- deferred

Exit criteria:
- README wording can point to one source of truth

## 6. Test Plan

### 6.1 Unit/backend structure tests

Required:
- type mapping tests
- builder emission tests
- backend fail-fast tests
- golden output tests for supported subset examples

### 6.2 CLI proof

Required:
- `simple compile --backend=vhdl` success on supported examples
- correct output path creation
- explicit error on unsupported inputs

### 6.3 Toolchain validation

Required:
- GHDL analyze (`-a`)
- GHDL elaborate (`-e`)
- optional GHDL run for simulation-backed examples

### 6.4 Simulation-backed proof

Required for the stronger completion milestone:
- one generated design actually runs in simulation
- one reference RV32 or similar design proves signal/state behavior

### 6.5 Negative and boundary tests

Required:
- unsupported MIR rejected
- unsupported types rejected
- unsupported dynamic/runtime constructs rejected
- invalid generated artifacts do not pass silently

## 7. Documentation Plan

Update:
- backend docs
- VHDL design docs
- CLI/backend guide
- example classification docs
- README feature wording

Required public wording after completion:
- VHDL backend supports a documented restricted hardware subset
- generated output is validated by GHDL
- simulation support is scoped to the published supported lanes

## 8. NFR Targets

### Correctness

- supported subset never emits misleading partial VHDL
- unsupported constructs fail fast
- GHDL validation is part of the proof, not optional folklore

### Maintainability

- subset rules live in one place
- example classification stays clean
- docs distinguish backend lowering from builder demos

### Tooling

- CLI behavior is deterministic
- toolchain absence yields explicit skip/fail diagnostics

## 9. Recommended Public State After Completion

After Phases 1 through 7 are complete, the repo can describe the VHDL backend as:

- a supported backend for a restricted hardware-oriented Simple subset
- strict and fail-fast on unsupported constructs
- validated through GHDL analysis/elaboration
- optionally simulation-backed for the published supported target lane(s)

At that point it can move from:
- experimental

to:
- supported with a clearly bounded hardware subset

without overclaiming arbitrary language-to-hardware compilation.

## 10. Immediate Next Steps

1. Freeze the supported hardware-oriented subset.
2. Finish strict subset validation and diagnostics.
3. Make `simple compile --backend=vhdl` authoritative for that subset.
4. Add GHDL analyze/elaborate proof for generated output.
5. Decide whether `riscv32_sim_vhdl` is part of this milestone or explicitly deferred.
