# SimpleOS Desktop Core Formal Verification — Detail Design

**Date:** 2026-04-18  
**Requirement:** [simpleos_desktop_core_formal_verification](../02_requirements/feature/simpleos_desktop_core_formal_verification.md)

## Design Goal

Produce a research-first verification package that is immediately usable by later implementation and verification phases without requiring another round of boundary decisions.

## Proof Decomposition

### Kernel-core slice

The first proof/spec slice is built from deterministic and pure surfaces:

1. initial privilege setup
2. trap classification
3. syscall register marshalling
4. syscall result write-back
5. capability/grant/scheduler invariants documented as contracts and referenced by later proof units

Immediate executable evidence:

- `rv64_user_mode_exec_spec.spl`
- new `simpleos_desktop_core_formal_verification_spec.spl`

### Desktop-contract slice

The first desktop slice is limited to deterministic contract surfaces:

1. window-selection uniqueness via `AppSwitcher`
2. crash-containment defaults via `CrashPolicy`
3. desktop-session readiness markers via planned system tests

This keeps the first desktop slice free from:

- framebuffer correctness proofs
- browser/layout proofs
- device/input-driver proofs

## Artifact Plan

### Research and requirements

- local and domain research docs
- feature and NFR options docs
- final feature and NFR docs

### Architecture and design

- architecture doc defining proof layers and assumption ledger
- detail design defining proof decomposition and evidence mapping
- system-test plan
- agent task breakdown

### Spec package

One OS feature spec must check both layers:

- kernel: privilege/trap/syscall invariants
- desktop: selection uniqueness and crash-containment defaults

## Test Structure

### Kernel tests

- user-vs-kernel privilege return state remain distinct
- trap classification preserves user `ecall` versus interrupt separation
- syscall ABI mapping remains stable

### Desktop tests

- app-switcher selection remains unique and wraps correctly
- closing a selected window preserves a valid remaining selection state
- crash-containment defaults do not treat user apps as kernel-resident components

### Later system evidence

- QEMU desktop lane must emit:
  - `boot`
  - `shell-ready`
  - `launcher-ready`
  - `desktop-ready`
  - `shortcut:ok`
  - `wm:ok`

Those checks are part of the later verification-bearing phase, not the current pure-spec milestone.

## Failure Modes

- over-claiming a desktop proof when only kernel slices are proved
- relying on permissive harnesses as if they were proof artifacts
- allowing assumption-heavy behavior to be reported without an assumption label
- treating the broken verifier status path as an available future gate

## Follow-On Work

1. repair `bin/simple verify status`
2. formalize capability/grant invariants in proof-bearing form
3. formalize scheduler lifecycle invariants in proof-bearing form
4. strengthen desktop-session provenance and readiness system specs
5. add later architecture-specific proof lanes only after the current claim package is stable
