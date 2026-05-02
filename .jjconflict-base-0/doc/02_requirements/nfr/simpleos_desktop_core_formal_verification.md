# SimpleOS Desktop Core Formal Verification — NFR Requirements

**Feature:** `simpleos_desktop_core_formal_verification`  
**Date:** 2026-04-18  
**Status:** Draft  
**Selected Option:** [Staged Assurance Matrix](simpleos_desktop_core_formal_verification_options.md)  
**Related:** [Feature Requirements](../feature/simpleos_desktop_core_formal_verification.md)

## Non-Functional Requirements

- **NFR-SODCFV-001 Evidence truthfulness**: every report and doc must distinguish proof evidence from test evidence and from assumptions.
- **NFR-SODCFV-002 Deterministic core contracts**: the kernel-core proof slice must focus on deterministic, pure, or specification-friendly surfaces first.
- **NFR-SODCFV-003 No silent degradation**: unsupported proof targets or unverified behaviors must be labeled explicitly, never implied as covered.
- **NFR-SODCFV-004 Assumption visibility**: the assumption ledger must appear in the architecture/design package and in later verification reports.
- **NFR-SODCFV-005 Stable public boundaries**: the research-first milestone must not change the external syscall ABI or desktop launch contract.
- **NFR-SODCFV-006 Proof-first CLI honesty**: no later proof-bearing milestone may claim repo-native verification readiness until the `bin/simple verify status` path is repaired and demonstrably usable.
- **NFR-SODCFV-007 Desktop target stability**: x86_64 remains the primary desktop evidence target until a later milestone broadens platform coverage explicitly.
- **NFR-SODCFV-008 Layer separation**: kernel proofs and desktop contracts must remain separable so later deeper proof work can advance the kernel without forcing premature GUI proof claims.
- **NFR-SODCFV-009 Reproducible evidence**: system-test evidence for the desktop layer must use named markers or deterministic pure specs instead of ad hoc manual inspection.
- **NFR-SODCFV-010 Documentation discipline**: future docs must update the same package when the proof boundary, assumptions, or claim wording changes.

## Verification Strategy

- Pure/spec tests for kernel-core seams already modeled in Simple code.
- Pure/spec tests for selected desktop invariants that do not require full GUI execution.
- QEMU-backed system evidence for desktop readiness markers, but never represented as proof.
- A later proof-bearing phase may deepen kernel proofs only after the verifier status path is repaired.
