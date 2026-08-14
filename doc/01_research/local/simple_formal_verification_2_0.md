<!-- codex-research -->
# Simple Formal Verification 2.0 — Local Research

**Date:** 2026-08-12
**Recovered and revalidated:** 2026-08-14
**Status:** Consolidated audit; implementation must revalidate line-level findings before editing

## Existing strengths

The repository already provides the language-facing proof vocabulary (`@verify`, `@ghost`, `@trusted`, contracts, invariants, `decreases`, `proof uses`, embedded `lean {}`, and external Lean projects), deterministic generation/checking infrastructure, proof ownership/collision gates, critical-profile fail-closed policy, numerous domain models, RISC-V HWIR/RVFI/SBY scaffolding, and compiler-admission/provenance work.

Relevant existing anchors include:

- `doc/04_architecture/infra/misc/lean_verification_contract.md`
- `doc/05_design/infra/verification_improvements_plan.md`
- `doc/03_plan/cert/formal_codegen_semantics_plan.md`
- `doc/01_research/infra/aop/lean_verification_with_aop.md`
- `doc/04_architecture/riscv_gen2_hwir_foundation.md`
- `doc/01_research/os/simpleos/desktop/simpleos_desktop_core_formal_verification*.md`
- `src/verification/**`

## Architectural gaps

1. The established proof-state contract can over-compress model checking and implementation verification into one `verified` state.
2. Existing generated contract shapes can establish mathematical postcondition satisfiability without connecting the returned witness to actual translated execution.
3. The current formal corpus is primarily separately written domain models; the codegen semantics plan independently records the missing HIR/MIR/backend preservation chain.
4. Machine integer lowering through mathematical integers/naturals is inadequate for compiler, OS, firmware, and RTL claims.
5. String-oriented expression/operator generation and fallback placeholders prevent exhaustive typed semantic coverage.
6. Name/prefix-oriented effect checks are not a sound substitute for typed transitive effects.
7. AOP model/runtime/compiler discrepancies mean pre-weave or independently modeled proofs cannot close the executed program.
8. Proof success based on build status/text scanning is weaker than transitive dependency and axiom/trust auditing.
9. Current RISC-V truthfulness gates correctly reject placeholder generated RTL; those gates must remain strict while a real RV32I slice is introduced.
10. Whole-project verification without a semantic dependency DAG/cache will be too slow and prone to stale evidence.

## Reuse decisions

- Preserve existing abstract Lean projects and relabel them `model_proven` until refinement is checked.
- Extend the existing assurance resolver with `verified`; do not create a parallel mode.
- Reuse the existing proof syntax and external Lean channel; do not expand Simple grammar.
- Extend current RISC-V HWIR, retirement, manifest, and fail-closed proof infrastructure.
- Integrate the existing compiler translation-validation plan as the first backend-refinement strategy.

## 2026-08-14 current-main annotation

Current main now contains typed `DecisionProbe` and `ConditionProbe` MIR opcodes, deterministic JSON serialization, optimizer/visitor preservation, and fail-closed probe admission. This is an incremental evidence-identity bridge, not closure of gaps 1–10: admitted probes still report `MIRCOV-PROBE-E-UNLOWERED`, and no current-main search found the selected four-state claim model or a `VerificationIR` implementation. The historical gap analysis therefore remains applicable, with the MIR bridge recorded as partial progress rather than overwritten as completion.

The listed architecture, design, plan, AOP research, and RISC-V HWIR anchor files remain present on current main. Exact corpus counts are intentionally not frozen here because concurrent formal lanes change them; verification must derive inventories from the revision under review.

## Required follow-up inventories

Before FV-0/FV-1 implementation, record exact owning modules and tests for contract generation, Lean expression/type lowering, proof-result parsing, assurance resolution, AOP expansion/weaving, compiler pass manifests, HWIR retirement/RVFI generation, and artifact provenance. This research deliberately defines the cross-repository finding without assigning dirty files that may belong to concurrent lanes.
