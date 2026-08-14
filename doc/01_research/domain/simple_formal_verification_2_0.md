<!-- codex-research -->
# Simple Formal Verification 2.0 — Domain Research

**Date:** 2026-08-12
**Recovered:** 2026-08-14
**Status:** Consolidated from the user-provided research brief; external version claims require compatibility-lane revalidation

## Findings adopted

- **CompCert/CakeML/Cogent:** Compiler assurance must connect source semantics to emitted code. Per-program certification/translation validation is the pragmatic first step; universal pass proofs can follow.
- **seL4/CertiKOS:** OS verification scales through explicit abstract interfaces and compositional refinement layers with a carefully stated trusted computing base.
- **FSCQ/Perennial:** Storage correctness must quantify over crash points and recovery, not only failure-free execution.
- **NASA SPIN/JPF work:** Bounded exploration is valuable for discovering concurrency traces, but manually maintained shadow models create translation risk.
- **Copilot/FRET:** Environmental assumptions that cannot be discharged statically can become bounded generated runtime monitors with explicit failure policy.
- **Sail/RVFI/riscv-formal:** RISC-V assurance needs an independent ISA oracle and an architectural retirement interface; neither proves the hardware generator by itself.
- **Kami/Kôika:** A hardware IR needs executable transition semantics and a checked relation to generated circuits.
- **Mutation/vacuity research:** A green proof is insufficient without reachable antecedents/covers and sensitivity to meaningful implementation/property mutations.
- **Lean ecosystem:** Lean is the proof-composition kernel and primary theorem environment; certificate-replayed SAT/SMT, bounded model checking, FP tooling, and RTL engines are complementary typed evidence providers.

## Resulting policy

No engine is accepted by brand or exit code alone. Every result carries a typed outcome and trust class. Independent references must not be generated solely from the implementation under test. Full-state whole-system proof is not an initial milestone; the program closes narrow vertical slices and composes them through frozen refinement interfaces.

## Tool/version note

The proposal supplied a Lean 4.30-to-4.33 migration recommendation dated 2026-08-12. This recovered document does not promote that historical recommendation to a current compatibility claim. Implementation must verify repository pins, release availability, Mathlib compatibility, checker compatibility, and tactic/BitVec/Float behavior in a dedicated lane before changing the pinned toolchain. The architecture depends on pinned reproducible versions, not on a particular unvalidated version number.
