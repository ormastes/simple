# SimpleOS Desktop Core Formal Verification — Requirements

**Feature:** `simpleos_desktop_core_formal_verification`  
**Date:** 2026-04-18  
**Status:** Draft  
**Selected Option:** [Bounded Kernel Proof + Constrained Desktop Contract](simpleos_desktop_core_formal_verification_options.md)  
**Related:** [Local Research](../../01_research/local/simpleos_desktop_core_formal_verification.md), [Domain Research](../../01_research/domain/simpleos_desktop_core_formal_verification.md)

## Motivation

SimpleOS already has:

- a real OS/kernel tree
- desktop/session behavior
- QEMU evidence lanes
- a repo-native contract and Lean-verification stack

What it does not yet have is a coherent and honest formal-verification package for the SimpleOS core.

This feature establishes that package for **both layers**:

- the **kernel core** as the proof-bearing surface
- the **desktop session** as a constrained contract surface above it

## In Scope

- **REQ-SODCFV-001**: Define a single formal-verification boundary for the SimpleOS kernel core and the desktop-session contract above it.
- **REQ-SODCFV-002**: Treat the kernel core as the primary proof-bearing surface for:
  - privilege return state
  - trap classification
  - syscall ABI marshalling
  - capability / grant authorization requirements
  - scheduler lifecycle invariants
  - VM isolation requirements
- **REQ-SODCFV-003**: Treat the desktop layer as a constrained contract surface for:
  - window ownership identity preservation
  - focus uniqueness
  - launcher-to-window provenance
  - crash-containment defaults
  - canonical desktop-session readiness markers
- **REQ-SODCFV-004**: Every verification artifact must classify evidence explicitly as:
  - `proved`
  - `model-checked`
  - `spec-checked`
  - `system-tested`
  - `assumed`
- **REQ-SODCFV-005**: The verification package must include an explicit assumption ledger covering at least:
  - hardware behavior
  - boot/setup trust
  - DMA/device behavior outside proof scope
  - QEMU oracle limits
  - unverified GUI/device/input behavior
- **REQ-SODCFV-006**: Public documentation must not claim that the full SimpleOS desktop is formally verified end to end.
- **REQ-SODCFV-007**: The package must include a seed OS feature spec that checks both:
  - a kernel-core invariant slice
  - a desktop-contract invariant slice
- **REQ-SODCFV-008**: Existing narrow OS proof work, especially `rv64_user_mode_exec`, must remain valid and serve as an input example rather than being replaced.
- **REQ-SODCFV-009**: The x86_64 desktop session is the primary desktop target for this feature.
- **REQ-SODCFV-010**: RV64 proof work is an architectural reference and reusable kernel seam, not the desktop target for this milestone.

## Out of Scope

- claiming full end-to-end formal verification for all of SimpleOS
- full boot-chain proof
- DMA/device-driver correctness proof
- full compositor/render/browser proof
- formal proof of arbitrary GUI interaction semantics
- hardware-specific source-to-binary proof parity across all architectures
- fixing all verification-tooling issues in the same milestone

## Acceptance Criteria

1. The repo contains a research package that explains the selected verification boundary and why stronger claims are not yet justified.
2. The repo contains final feature and NFR requirements aligned with a staged-assurance approach.
3. The repo contains an architecture doc that names the proof-bearing kernel-core surfaces, the constrained desktop surfaces, and the assumption ledger.
4. The repo contains a design doc, system-test plan, and agent-task plan for later proof-bearing work.
5. The repo contains a new OS spec that exercises both the kernel and desktop slices without tautological assertions.
6. Existing `rv64_user_mode_exec` proof/spec behavior still passes unchanged.
7. No new documentation claims stronger assurance than the current evidence supports.

## Dependencies

- `doc/04_architecture/simpleos_interfaces.md`
- `doc/04_architecture/lean_verification_contract.md`
- `doc/04_architecture/rv64_user_mode_exec.md`
- `src/os/kernel/arch/riscv64/trap_model.spl`
- `src/os/crash_policy.spl`
- `src/os/desktop/app_switcher.spl`
- `src/os/qemu_runner.spl`

## Claim Policy

Allowed claim:

- “SimpleOS has bounded formal verification for defined kernel-core properties, with constrained desktop-session contracts and explicit assumptions.”

Disallowed claims:

- “SimpleOS desktop is fully formally verified.”
- “SimpleOS matches seL4 assurance.”
- “QEMU desktop validation is a proof.”
