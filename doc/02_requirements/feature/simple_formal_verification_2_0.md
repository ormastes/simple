<!-- codex-design -->
# Simple Formal Verification 2.0 — Feature Requirements

**Status:** Selected baseline
**Date:** 2026-08-12
**Recovered:** 2026-08-14
**Scope:** Simple language, SimpleOS, and generated RISC-V hardware

The user-provided Formal Verification 2.0 proposal is the selected requirement baseline. This document turns it into traceable requirements; it does not claim that the implementation exists. Current-main partial implementations, including the fail-closed MIR evidence bridge, remain subject to these requirements and do not imply end-to-end completion.

## Product claim

Formal verification means a reproducible refinement chain from the exact typed, macro-expanded, canonically woven Simple program to its deployed binary, OS image, RTL, or synthesized artifact. Every transformation is covered by a proof, a checked per-build certificate, a declared bounded trusted boundary, or a verified runtime monitor.

## Requirements

- **REQ-FV2-001 — Truthful status:** Reports distinguish `model_proven`, `source_refined`, `backend_refined`, and `artifact_verified`. Only the last permits an unqualified verified-artifact claim.
- **REQ-FV2-002 — Verified profile:** Add `verified` above `critical` through the existing typed assurance-profile resolver and SDN configuration; add no language mode or verification grammar.
- **REQ-FV2-003 — Canonical program:** Macro expansion and deterministic AOP weaving complete before Verification IR (VIR); proof and compilation consume the same canonical program.
- **REQ-FV2-004 — Execution-linked contracts:** Preconditions and normal/error postconditions refer to actual function execution and state transitions. An existential result disconnected from execution is forbidden.
- **REQ-FV2-005 — Typed VIR:** Versioned `VerificationIR v1` carries stable symbol/source identity, exact types, effects, ownership, contracts, call closure, trust references, and semantic classification.
- **REQ-FV2-006 — Exact semantics:** Machine integers preserve width, signedness, overflow, shifts, and representation. Every reachable construct is `exact`, `abstracted_with_refinement`, `external_with_contract`, or `unsupported`; verified rejects unsupported and implicit fallbacks.
- **REQ-FV2-007 — Typed Lean generation:** A typed Lean IR precedes deterministic pretty-printing. String-oriented operator semantics, guessed types, `_`, and generated uninterpreted definitions are forbidden in verified closure.
- **REQ-FV2-008 — Proof obligations:** Generate well-formedness, satisfiability, termination/boundedness, memory/ownership, effect/frame, normal/error result, invariant, call compatibility, non-vacuity, lowering coverage, and trust-closure obligations.
- **REQ-FV2-009 — Trust audit:** Release roots receive transitive axiom/trust audits, fresh checking, and independent replay. `sorry`, `admit`, undeclared axioms, unchecked solver success, and untracked native-evaluation trust block release.
- **REQ-FV2-010 — Evidence:** Versioned receipts bind proof roots, dependencies, tools, policies, assumptions, semantic hashes, compiler lineage, and final artifact hashes.
- **REQ-FV2-011 — AOP/macros:** Exact join points, order, introduced symbols, and expansion/weave hashes enter closure and cache identity. Post-VIR semantic transforms require refinement evidence.
- **REQ-FV2-012 — Effects:** Effect enforcement uses typed transitive effect sets, not names or prefixes.
- **REQ-FV2-013 — Compiler relation:** Begin with per-build translation validation for selected passes and targets; later universal pass proofs may replace validators.
- **REQ-FV2-014 — SimpleOS slice:** Prove one vertical implementation-linked slice spanning capabilities, process lifecycle, bounded IPC, scheduling, mapping, and crash-safe storage.
- **REQ-FV2-015 — RISC-V chain:** Use an independent Sail ISA oracle, canonical HWIR retirement semantics, generated RVFI, riscv-formal/SBY, HWIR-to-RTL refinement, and post-synthesis equivalence.
- **REQ-FV2-016 — Adversarial assurance:** Critical suites include satisfiability/cover witnesses plus property, implementation, stale-cache, and evidence mutation.
- **REQ-FV2-017 — Dynamic boundaries:** Dynamically loaded code must carry compatible signed receipts and discharge composition obligations or remain an explicit bounded TCB boundary.
- **REQ-FV2-018 — No new proof syntax:** Reuse `@verify`, `@ghost`, `@trusted`, contracts, invariants, `decreases`, `proof uses`, `lean {}`, and external Lean modules.
- **REQ-FV2-019 — Fail closed:** Missing tools, timeout, `unknown`, stale evidence, unsupported lowering, and environment failure never become pass.
- **REQ-FV2-020 — Staged delivery:** Gates progress through truthfulness, exact semantics, VIR/compiler relation, AOP closure, SimpleOS slice, RV32I, RV64/privilege/MMU, and verified release.

## Explicit non-goals

- Recreating Lean syntax in Simple.
- Claiming whole-system verification from separately handwritten models.
- Proving every compiler pass universally in the first delivery.
- Treating RVFI as proof of HWIR generator correctness or side-channel security.
- Weakening current fail-closed RISC-V placeholder gates.
