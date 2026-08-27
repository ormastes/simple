# Feature: Simple Formal Verification 2.0

## Raw Request

`$sp_dev impl the formal verification plan.`

The authoritative plan and requirements are:

- `doc/02_requirements/feature/simple_formal_verification_2_0.md`
- `doc/02_requirements/nfr/simple_formal_verification_2_0.md`
- `doc/04_architecture/simple_formal_verification_2_0.md`
- `doc/05_design/simple_formal_verification_2_0.md`
- `doc/03_plan/agent_tasks/simple_formal_verification_2_0.md`
- `doc/03_plan/sys_test/simple_formal_verification_2_0.md`

## Task Type

feature

## Refined Goal

Implement the complete fail-closed Formal Verification 2.0 refinement and evidence chain for verified Simple programs, the selected SimpleOS vertical slice, and staged generated RISC-V artifacts, with truthful status from model proof through artifact identity.

## Acceptance Criteria

- **AC-1 — Truthful status:** The typed assurance/reporting pipeline implements the complete `FormalStatus v1` lattice, migrates legacy proof results conservatively, and tests prove that model-only evidence cannot produce `source_refined`, `backend_refined`, or `artifact_verified`.
- **AC-2 — Verified profile:** The existing typed assurance resolver and SDN configuration accept `verified` above `critical`; the profile is fail-closed for stale, missing-tool, timeout, unknown, admitted, unsupported, and unapproved-trust outcomes, with no new grammar or parallel language mode.
- **AC-3 — Canonical program:** Deterministic macro expansion and exact AOP weaving finish before verification lowering; proof and compilation bind to the same woven semantic hash and exact ordered `WeaveManifest v1`.
- **AC-4 — Execution-linked contracts:** Generated normal, error, frame, invariant, and termination obligations quantify over actual translated execution outcomes; a deliberately wrong body fails even where an existential mathematical result satisfies the postcondition.
- **AC-5 — Typed VIR:** `VerificationIR v1` and `SemanticCoverage v1` are implemented in pure Simple with stable SymbolIds/source maps, exact types/representations, effects, ownership/capabilities, contracts, transitions, calls, trust references, canonical serialization, semantic hashes, and exhaustive fail-closed lowering.
- **AC-6 — Exact core semantics:** Machine integers preserve width, signedness, overflow mode, shifts, and representation; Result, enums, aggregates, arrays, text, pointers/references, mutation, extern/SFFI, and supported async/state-machine constructs are exact or carry checked refinement/contracts, never guessed types, `_`, or uninterpreted fallback definitions.
- **AC-7 — Typed Lean IR:** Pure-Simple typed Lean IR validates definitions, types, terms, patterns, binders, theorems, and proof references before deterministic printing; string-oriented operator semantics and unsupported fallback emission are rejected.
- **AC-8 — Typed effects and proof obligations:** Transitive effect/ownership closure catches direct, indirect, aliased, method, generated, macro, and aspect calls; `ProofObligation v1` covers well-formedness, satisfiability, termination/bounds, memory/ownership, effect/frame, result/error, invariants, call compatibility, non-vacuity, lowering coverage, and trust closure.
- **AC-9 — Trust and evidence:** `ProofReceipt v1`, `TrustManifest v1`, and `VerificationCacheKey v1` bind proof roots, transitive dependencies/axioms, tools, tactic/solver/trust policy, macro/weave/compiler lineage, semantic inputs, and final artifact hashes; fresh checking and configured independent replay reject `sorry`, `admit`, undeclared axioms, unapproved native trust, forged/stale evidence, and checker disagreement.
- **AC-10 — Compiler refinement:** `CompilerCertificate v1` provides checked per-build translation validation for the staged pass/backend subset, an intentionally unsound rewrite is rejected, and no final artifact status exceeds the weakest checked compiler edge.
- **AC-11 — Incremental performance:** SymbolId/SCC proof scheduling and semantic cache invalidation cover edits to types, dependencies, pointcuts, layouts, tools, policies, targets, and trust; formatting-only edits retain valid semantic hits; timing, hit/miss, invalidation, critical-path, and RSS evidence is exposed.
- **AC-12 — Adversarial assurance:** Every critical implication/invariant/property family has satisfiable/reachable or cover witnesses, and non-equivalent property, implementation, stale-cache, forged-receipt, AOP-order, compiler-pass, RVFI, and hardware mutations turn the relevant gate red.
- **AC-13 — SimpleOS vertical slice:** Abstract capability, process, bounded IPC, scheduler, map/unmap, and transactional recovery models refine the exact woven SimpleOS implementation/VIR; bounded concurrency/crash counterexamples map to source events; environmental assumptions are monitored where feasible or remain explicit bounded-TCB entries.
- **AC-14 — RISC-V end-to-end:** A real generated RV32I core replaces placeholder status for the admitted slice; canonical HWIR retirement generates RVFI; Sail differential, riscv-formal/SBY, HWIR-to-RTL, covers/mutations, and RTL-to-netlist equivalence bind to `HardwareProofReceipt v1`, then the staged RV64/privilege/MMU/trap/interrupt/Linux gates are implemented without weakening current gates.
- **AC-15 — Dynamic composition:** Dynamic plugins/aspects load into verified artifacts only with compatible signed receipt, interface/profile/compiler lineage, and discharged composition obligations; otherwise they are explicit bounded-TCB boundaries and cannot claim closed verification.
- **AC-16 — Executable specifications:** Focused unit/integration tests and `test/03_system/compiler/formal_verification_2_0_spec.spl` trace every `REQ-FV2-001` through `REQ-FV2-020`, use real fail-closed oracles and built-in matchers, reach the branch-coverage target, and generate a reviewed operator-quality mirrored manual with zero stubs and acceptable `sspec-maintain` scores.
- **AC-17 — Verification gates:** Applicable focused tests, changed-file lint, duplication check, compiler/core/lib/MCP/LSP checks, env-runtime audits, full release-bound SPipe suite, Lean/checker replay, RISC-V proof/equivalence gates, and `find doc/06_spec -name '*_spec.spl' | wc -l = 0` each pass once on the final unchanged implementation; verification reports `STATUS: PASS` only after every umbrella criterion has authoritative evidence.
- **AC-18 — Knowledge and tracking:** Research, requirements, architecture, detail design, implementation/system-test plans, generated manual, and developer/operator guides are current; feature expert `doc/00_llm_process/feature_expert/formal_verification/skill.md` and compiler/OS/hardware layer-expert skills are added or updated; every discovered unfixed gap has a `doc/08_tracking/bug/` record with file:line and unblock condition. Verification-contract changes also update affected `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, `.claude/commands`, and `.gemini/commands`, or record concrete N/A reasons.

## Scope Exclusions

- Recreating Lean syntax or dependent-program grammar in Simple.
- Treating manually maintained shadow models, RVFI alone, simulation alone, or ordinary tests as the complete proof chain.
- Side-channel-security claims from architectural RISC-V conformance.
- Release/version bump/tag/push; those require a later explicit release request and verified PASS.

## Cooperative Review

- Lower-model sidecars: bounded inventories/test matrices may use Codex Spark, Claude Haiku, or Claude Sonnet after the frozen v1 interface names below are accepted; they may not make broad done/exclusion claims.
- Merge owner: primary Formal Verification 2.0 implementation agent.
- Final reviewer: independent best available normal/highest-capability agent.
- Frozen interfaces: `VerificationIR v1`, `SemanticCoverage v1`, `ProofObligation v1`, `ProofReceipt v1`, `TrustManifest v1`, `WeaveManifest v1`, `CompilerCertificate v1`, `HardwareProofReceipt v1`, `FormalStatus v1`, `VerificationCacheKey v1`.
- Manual flow steps: `step("Resolve the verified closure")`, `step("Generate canonical verification semantics")`, `step("Discharge proof and trust obligations")`, `step("Validate compiler and artifact refinement")`, `step("Audit the final evidence bundle")`.
- Setup/checker helpers: `setup_formal_verification_fixture`, `check_formal_status`, `check_semantic_identity`, `check_proof_receipt`, `check_compiler_certificate`, `check_hardware_receipt`.
- Any unfinished helper must use `assert(false)` or `fail(...)`; silent placeholders are forbidden.
- Generated-manual review owner: primary agent, followed by independent final reviewer.

## Phase

dev-in-progress

Overall status: blocked — source development is present, but canonical Stage 4
execution, external proof material, and final verification remain incomplete.

Overall status: blocked — source development is present, but canonical Stage 4
execution, external proof material, and final verification remain incomplete.

## Log

- dev: Reconstructed the accepted feature baseline and created 12 testable
  acceptance criteria with parallel ownership and highest-capability review.
- recovery: rebased the owned lane onto wave 2, rejected Rust-seed evidence,
  closed bounded source-level fail-open paths, and retained blocked status.
- parallel-hardening: bound proof work recursively with framed SHA-256,
  hardened VIR membership and RV64 authority diagnostics, and disabled
  caller-built replay/VC/Gate-3 promotion pending canonical producers.
- recovery-v2: routed additive Wave 6 through resolved VIR coverage, inventoried
  every MIR terminator, blocked Exact rows without a transition manifest, bound
  V3 signer membership, and disabled legacy CLI policy downgrade; authoritative
  runtime, atomic policy provenance, and external proof evidence remain blocked.
