# GHDL RV32 Semihost Simulation Completion Plan

**Date:** 2026-04-04  
**Status:** Ready for concurrent implementation  
**Execution model:** parallel agents with bounded ownership  
**Scope:** complete the GHDL-backed RV32 **semihost** simulation lane as far as possible **without** making mailbox transport a blocker  
**Primary target:** promote the existing semihost/GDB-backed GHDL lane from "in progress" to a bounded supported simulation lane  

## Why This Plan Exists

The current repo already has substantial GHDL coverage:

- a working GHDL adapter in [adapter_ghdl_rv32.spl](src/lib/nogc_sync_mut/debug/remote/exec/adapter_ghdl_rv32.spl)
- a semihost-based feature proof in [ghdl_riscv32_semihost_spec.spl](test/feature/baremetal/ghdl_riscv32_semihost_spec.spl)
- a composite-runner proof in [ghdl_rv32_composite_runner_spec.spl](test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl)
- lane registration and capability reporting in:
  - [lane_registry.spl](src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl)
  - [lane_status.spl](src/lib/nogc_sync_mut/debug/remote/exec/lane_status.spl)
  - [lane_matrix.md](doc/08_tracking/lane_matrix.md)

The reason the lane is still `in_progress` is narrower than the full GHDL stack:

- the mailbox-backed simulated remote-interpreter lane is still open
- the current proof story is semihost/GDB-backed, not mailbox-backed
- the public docs still group all of GHDL under the larger unfinished mailbox story

This plan intentionally splits the problem:

1. complete the **semihost/GDB-backed GHDL simulation lane** and promote it honestly
2. keep the **mailbox-backed remote-interpreter lane** as a follow-on phase, not a blocker

## Completion Target

This plan is successful when the repo can honestly advertise:

- `GHDL RV32 semihost simulation is implemented with bounded scope`

Meaning:

- GHDL can run checked-in RV32 ELF workloads through the current simulation flow
- the remote baremetal composite runner can compile and execute small RV32 workloads through GHDL
- capability detection, runner integration, and result parsing are deterministic
- docs clearly distinguish this completed semihost lane from the unfinished mailbox lane

It does **not** require:

- mailbox MMIO transport
- full simulated remote-interpreter command protocol
- Simple-defined RV32 hardware replacing handwritten RTL

## Supported Slice To Promote

### In scope

- `ghdl` presence probing
- GDB connection to a running GHDL simulation
- semihost-text result collection
- compile-upload-run-return-value execution for bounded RV32 workloads
- checked-in ELF smoke proofs
- composite runner proof through `CompilerBridge`
- lane metadata and status publication
- deterministic skip behavior when host tools are absent

### Explicitly out of scope

- mailbox protocol
- testbench-side mailbox driver
- target-side mailbox runtime binding
- promotion of `riscv32_sim_vhdl` as a mailbox-backed remote-interpreter lane
- FPGA board/JTAG proof

## Public Status Goal

After this plan completes:

- `ghdl_rv32_sim` should be split in public docs into:
  - **GHDL RV32 semihost simulation:** implemented with bounded scope
  - **GHDL mailbox-backed remote interpreter:** deferred / in progress

This avoids keeping the working GHDL slice hidden behind the still-open mailbox milestone.

## Agent Workstreams

### Agent A: Capability and Adapter Closure

**Owns**
- [adapter_ghdl_rv32.spl](src/lib/nogc_sync_mut/debug/remote/exec/adapter_ghdl_rv32.spl)
- GHDL capability probes
- GDB connection lifecycle behavior

**Tasks**
- verify the adapter supports:
  - connect
  - disconnect
  - write code
  - read code
  - register read/write
  - resume
  - halt/wait
- normalize error paths so the lane reports:
  - missing `ghdl`
  - missing `clang`
  - missing `ld.lld`
  - missing `llvm-objcopy`
  - GDB connect failure
  - simulation launch/connect timeout
- ensure `capability_report()` captures the real tool prerequisites for the semihost lane, not just `ghdl`

**Acceptance**
- semihost lane capability status is precise and not over-optimistic
- adapter failures are actionable and deterministic

### Agent B: Runner and Composite Execution Closure

**Owns**
- [ghdl_rv32_composite_runner_spec.spl](test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl)
- compiler bridge integration
- remote manager orchestration for GHDL

**Tasks**
- turn the current composite proof into the authoritative semihost simulation proof
- add coverage for:
  - return `0`
  - non-zero return
  - compile failure path
  - connect failure path
  - execution failure path
- ensure the same runner shape is consistent with the other remote lanes
- eliminate ad hoc skip behavior where the runner can instead assert a normalized capability result

**Acceptance**
- composite execution is no longer just a smoke test; it is the canonical bounded workload proof for GHDL

### Agent C: Semihost ELF Proof Pack

**Owns**
- [ghdl_riscv32_semihost_spec.spl](test/feature/baremetal/ghdl_riscv32_semihost_spec.spl)
- checked-in ELF fixtures
- runner script assumptions

**Tasks**
- promote the existing ELF proofs into a stable proof pack:
  - hello-world semihost text
  - exit path
  - checked-in SSpec ELF behavior
- verify the runner script contract:
  - ELF input
  - VHDL image conversion
  - GHDL invocation
  - output parsing
- add at least one negative case:
  - missing ELF
  - malformed ELF
  - GHDL timeout

**Acceptance**
- semihost ELF execution is independently proven, not only via composite compilation

### Agent D: Lane Classification and Docs Split

**Owns**
- [lane_registry.spl](src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl)
- [lane_matrix.md](doc/08_tracking/lane_matrix.md)
- [remote_baremetal_completion_2026-04-04.md](doc/09_report/remote_baremetal_completion_2026-04-04.md)
- GHDL-related public wording in [README.md](README.md) and audit docs if touched

**Tasks**
- split current GHDL language into:
  - completed semihost simulation lane
  - deferred mailbox lane
- decide whether `ghdl_rv32_sim` remains one lane with a scoped note, or is split into two documented sub-lanes:
  - `ghdl_rv32_semihost`
  - `ghdl_rv32_mailbox`
- update lane matrices and reports accordingly
- ensure public wording stops saying “GHDL incomplete” without clarifying that the semihost slice is already real

**Acceptance**
- docs accurately reflect that mailbox is the remaining blocker, not the whole GHDL simulation path

### Agent E: Test Runner and CI Readiness

**Owns**
- test entrypoint integration
- host-tool readiness behavior
- CI/slow-test classification for GHDL

**Tasks**
- define whether GHDL semihost specs are:
  - normal integration tests
  - `slow_it`
  - host-aware gated tests
- make skip behavior explicit and machine-readable where possible
- ensure one clear smoke command exists for local validation
- document recommended local smoke commands and CI inclusion policy

**Acceptance**
- GHDL simulation has a clear, repeatable validation path instead of ad hoc local knowledge

### Main Agent: Integration and Promotion

**Owns**
- final support statement
- merged report and status recommendation
- cross-agent consistency

**Tasks**
- review all changed tests and docs for consistency
- ensure mailbox is still explicitly listed as deferred
- promote only the semihost/GDB-backed slice
- publish one final status recommendation:
  - `Implemented with bounded scope`

## Test Matrix To Add Or Harden

### Semihost/GHDL smoke

- run hello-world ELF through GHDL and assert output marker
- run checked-in SSpec ELF through GHDL and assert success marker
- assert deterministic exit/stop behavior

### Composite runner

- compile `fn main() -> i64: 0` and assert result `0`
- compile `fn main() -> i64: 42` and assert result `42`
- compile invalid source and assert clean failure
- fail cleanly when GHDL tools are unavailable

### Adapter capability

- capability report distinguishes missing tool from connect failure
- adapter refuses manager creation before connect
- disconnect after failed connect is safe

### Negative cases

- malformed/missing ELF path
- timeout or no-halt path
- missing `ld.lld` / `llvm-objcopy` / `clang` on composite lane

## Execution Order

1. Agent A freezes the semihost adapter/tool prerequisite contract.
2. Agents B and C harden composite and ELF proofs in parallel.
3. Agent E cleans up runner/CI behavior once the proof shape is stable.
4. Agent D updates lane/docs wording last.
5. Main agent integrates and decides whether the lane can be promoted.

## Definition of Done

The non-mailbox GHDL slice is complete when:

- semihost ELF proof passes
- composite runner proof passes
- capability and failure modes are normalized
- docs distinguish semihost completion from mailbox incompleteness
- the lane can be honestly described as:
  - `Implemented with bounded scope`

## Remaining Work After This Plan

These remain explicitly open after this plan, by design:

- mailbox MMIO contract
- target-side mailbox runtime
- host-side mailbox reader in the testbench
- mailbox-backed remote interpreter execution
- promotion of a mailbox-backed `riscv32_sim_vhdl` lane

Those should move into a separate follow-on program rather than blocking semihost completion.
