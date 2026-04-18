<!-- codex-design -->
# SimpleOS Desktop Core Formal Verification — Architecture

**Date:** 2026-04-18  
**Requirement:** [simpleos_desktop_core_formal_verification](../02_requirements/feature/simpleos_desktop_core_formal_verification.md)

## Architecture Summary

This feature defines the verification architecture for **both layers** of the SimpleOS core:

1. a **kernel-core proof surface**
2. a **desktop-session contract surface**

The architecture is intentionally asymmetric:

- the kernel core is the primary machine-checkable target
- the desktop is constrained by explicit contracts and evidence labels

## Verification Layers

### Layer 1: Proof-bearing kernel core

This layer owns the strongest claims in scope:

- privilege return state
- trap classification
- syscall register marshalling and return write-back
- capability and grant authorization requirements
- scheduler lifecycle invariants
- VM isolation requirements

Primary artifacts:

- pure/spec code in `src/os/kernel/arch/riscv64/trap_model.spl`
- syscall and scheduler contracts already documented in `simpleos_interfaces.md`
- OS feature specs under `doc/06_spec/app/os/feature/`

### Layer 2: Constrained desktop-session contract

This layer does **not** attempt a full GUI proof.

It owns these narrower contracts:

- window ownership identity preservation
- focus uniqueness
- launcher-to-window provenance
- crash-containment defaults by fault domain
- canonical desktop-session readiness markers

Primary artifacts:

- `src/os/desktop/shell.spl`
- `src/os/desktop/app_switcher.spl`
- `src/os/crash_policy.spl`
- marker-driven QEMU lanes in `src/os/qemu_runner.spl`

### Layer 3: Assumption boundary

Everything below or outside the current proof boundary must be listed as an assumption or deferred proof target:

- boot chain
- hardware behavior
- DMA/device memory effects
- device-driver correctness
- full compositor/browser/render correctness
- non-pure GUI interaction semantics

## Evidence Taxonomy

All verification artifacts must classify evidence exactly as one of:

- `proved`
- `model-checked`
- `spec-checked`
- `system-tested`
- `assumed`

Rules:

- `proved` is reserved for machine-checked proof obligations in the repo’s formal pipeline
- `spec-checked` is reserved for executable repo specs such as SSpec-style OS feature specs
- `system-tested` is reserved for QEMU/runtime evidence
- `assumed` is mandatory wherever the proof model stops

## Interface Boundaries

### Kernel-core public boundaries

- syscall ABI defined in `doc/04_architecture/simpleos_interfaces.md`
- trap/runtime seam defined in `doc/04_architecture/rv64_user_mode_exec.md`
- Lean verification contract defined in `doc/04_architecture/lean_verification_contract.md`

### Desktop-session public boundaries

- shell/launcher/compositor identity boundary at the desktop shell
- desktop readiness markers emitted by named QEMU scenarios
- crash policy defaults used for fault-domain containment claims

## Design Rules

- Do not claim proof for the whole desktop when only kernel-core properties are proved.
- Do not represent QEMU success as proof.
- Do not widen the proof boundary silently when implementation grows.
- Keep proof-bearing kernel slices pure or specification-friendly first.
- Keep desktop constraints explicit, minimal, and tied to named artifacts.

## Assumption Ledger

The following assumptions are mandatory for this feature package:

1. boot/setup code establishes a valid initial kernel state
2. hardware behaves as modeled for the covered kernel seams
3. DMA-enabled or MMIO-heavy device behavior is outside the current proof coverage
4. QEMU is a runtime oracle for readiness/system evidence only
5. full compositor/render/browser/device correctness is not covered by this package

## Consequences

- future proof-bearing work can deepen kernel claims without implying that GUI correctness is fully proved
- desktop assurance can still improve through stronger specs and system evidence
- public documentation gains a stable, explicit ceiling for formal-verification claims
