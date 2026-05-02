<!-- codex-research -->
# Research: SimpleOS Desktop Core Formal Verification

**Date:** 2026-04-18  
**Scope:** Local repo analysis for a research-first formal-verification program covering both the SimpleOS kernel core and the desktop-session contract above it.

## Executive Summary

The repo already contains enough verification infrastructure to start a bounded SimpleOS formal-verification program, but not enough to honestly claim that the full desktop OS core is formally verified end to end.

Current local evidence supports a narrower and defensible target:

- formally specified and machine-checkable **kernel-core invariants**
- explicitly constrained **desktop-session invariants**
- an **assumption ledger** for the hardware, boot, DMA, and unverified GUI/runtime edges
- a strict claim policy that separates:
  - `proved`
  - `model-checked`
  - `spec-checked`
  - `system-tested`
  - `assumed`

## Existing Verification Infrastructure

### Formal plumbing already present

- `doc/04_architecture/lean_verification_contract.md`
  - defines the supported verification subset (`@verify`, `@ghost`, `@trusted`, contracts, invariants, `lean{}` blocks, generated proof units, cache state model)
- `doc/07_guide/lean_verification_workflow.md`
  - documents the intended Lean workflow
- `doc/report/unique_features.md`
  - claims a compiler-integrated verification stack and Lean generation support

### Repo-local proof slice already present

- `doc/04_architecture/rv64_user_mode_exec.md`
- `doc/05_design/rv64_user_mode_exec.md`
- `doc/06_spec/app/os/feature/rv64_user_mode_exec_spec.spl`

This is the clearest current example of a narrow, honest OS proof package:

- it proves a trap/runtime seam
- it does not over-claim Linux boot, simulator parity, or GUI completeness

### Current tooling limitation

- `bin/simple verify status` is currently not usable as a reliable program gate
- observed interpreter/export failures come from `src/app/verify/main.spl` dependency loading
- this is a blocker for any later “proof-bearing” phase that wants a repo-native formal-verification status command

## Current SimpleOS Core Boundary In Repo

### Kernel-core surfaces with realistic proof potential now

1. **Trap and syscall seam**
   - `src/os/kernel/arch/riscv64/trap_model.spl`
   - already exposes pure functions for:
     - initial privilege setup
     - trap classification
     - syscall register marshalling
     - syscall result write-back

2. **Frozen syscall ABI and service contracts**
   - `doc/04_architecture/simpleos_interfaces.md`
   - already documents the kernel syscall ABI, grant-related syscalls, and scheduler-facing contracts

3. **Capability / privilege / grant contracts**
   - referenced in `simpleos_interfaces.md` and current kernel types
   - suitable for requirement/spec-level non-escalation claims

4. **Scheduler and task lifecycle rules**
   - current docs already describe:
     - clone / exec / wait lifecycle
     - zombie collection
     - user-vs-kernel task distinction

5. **VM / privilege isolation seam**
   - existing docs make address-space separation and user-vs-kernel return state central to the runtime boundary

### Desktop-session surfaces with realistic constrained verification now

The desktop layer is broad, but some contract slices are narrow enough to specify safely:

1. **Window ownership and identity preservation**
   - `src/os/desktop/shell.spl`
   - shell applies remote-window creation and explicitly preserves process/app identity at the shell boundary

2. **Focus and selection uniqueness**
   - desktop shell and compositor markers exist
   - `src/os/desktop/app_switcher.spl` already exposes a pure window-selection model

3. **Crash containment defaults**
   - `src/os/crash_policy.spl`
   - gives stable policy defaults for:
     - user apps
     - system services
     - kernel components
     - baremetal domains

4. **Desktop boot/session markers**
   - `src/os/qemu_runner.spl` documents canonical desktop markers:
     - `boot`
     - `shell-ready`
     - `launcher-ready`
     - `desktop-ready`
     - `shortcut:ok`
     - `wm:ok`

These surfaces are appropriate for:

- spec-checked invariants
- system-test evidence
- claim-scoped desktop constraints

They are **not** enough for a credible full proof of:

- compositor correctness
- browser/layout correctness
- full GUI event semantics
- device/input correctness
- DMA/device safety

## Existing Local Evidence And Gaps

### Healthy evidence

- `doc/06_spec/app/os/feature/rv64_user_mode_exec_spec.spl` passes
- local SimpleOS research already exists:
  - `doc/01_research/local/simpleos_l4_exokernel_platform.md`
  - `doc/01_research/local/simpleos_qemu_validation.md`
- current QEMU validation reached:
  - headless boot pass
  - WM/GUI bring-up markers
  - tools lane pass with caveats
  - SSH/network lane with partial success

### Gaps that block over-claiming

1. **Desktop proofs are not present**
   - current desktop evidence is mainly runtime/QEMU-driven

2. **Harnesses can be permissive**
   - prior QEMU validation explicitly notes weak/passive success conditions in some lanes

3. **Kernel proof coverage is narrow**
   - there is no full proof package for:
     - capability non-escalation
     - endpoint authorization
     - scheduler invariants
     - desktop crash-containment properties

4. **Verification CLI is not a stable gate yet**
   - later phases must repair the verification status path before making stronger proof workflow claims

## Local Conclusions

### What the repo can support now

- a research-first package that freezes:
  - proof boundary
  - claim policy
  - assumption ledger
  - evidence taxonomy
  - kernel and desktop invariant set
- a seed OS feature spec that checks:
  - kernel privilege/trap/syscall invariants
  - desktop selection / containment defaults

### What the repo should not claim now

- “SimpleOS desktop core is formally verified”
- “full kernel is fully machine-proven”
- “QEMU desktop pass equals proof”
- “device, DMA, or boot chain are covered by current proofs”

## Recommended Verification Boundary

### In-scope formal core

- trap classification
- syscall ABI marshalling and result application
- privilege return state
- capability / grant authorization requirements
- scheduler lifecycle invariants
- VM / address-space isolation requirements

### In-scope constrained desktop contract

- window ownership identity preservation
- focus uniqueness
- launcher-to-window provenance requirement
- crash-containment defaults by fault domain
- canonical desktop boot/session markers for system-test evidence

### Explicit assumptions

- boot code correctness
- hardware behaves as modeled
- DMA-enabled devices are outside current proof coverage
- QEMU is an execution oracle, not a proof engine
- GUI/device/input behavior outside the pure model remains test-backed, not formally proved
