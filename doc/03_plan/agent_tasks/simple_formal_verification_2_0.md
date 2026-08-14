# Simple Formal Verification 2.0 — Canonical Integration Plan

**Status:** Active replacement lane; MIR evidence foundation partially implemented
**Date:** 2026-08-14
**Merge owner:** Primary FV2 integration agent in this isolated detached worktree
**Final reviewer:** Separate highest-capability `$verify` reviewer after reconciliation
**Historical input:** Accepted FV2 artifacts from the abandoned lane, including commit
`8257fde9eb1`; they define intent but are not current-main implementation evidence.

## Claim boundary

Formal Verification 2.0 is a fail-closed refinement chain from the exact
expanded and woven Simple program through MIR, proof checking, compiler
transforms, and the shipped artifact. A model proof is never an artifact proof.
Unknown, malformed, stale, unsupported, timed-out, or missing evidence blocks
promotion.

The selected baselines are `REQ-FV2-001..020` and `NFR-FV2-001..010`.
Research, requirements, architecture, and detail-design artifacts have been
restored, reviewed, and committed. The FV2 implementation capsule, modern
system spec, and manual mirror are present in this working tree; executable
admission remains blocked by the missing canonical Stage 4 runtime.

## Frozen shared interfaces and manual vocabulary

The shared names are `VerificationIR v1`, `SemanticCoverage v1`,
`ProofObligation v1`, `ProofReceipt v1`, `TrustManifest v1`,
`WeaveManifest v1`, `CompilerCertificate v1`, `HardwareProofReceipt v1`,
`FormalStatus v1`, and `VerificationCacheKey v1`. Incompatible changes require
a new version, migration coverage, and stale-cache rejection.

The system-manual flow is frozen as:

- `step("Audit the formal claim boundary")`
- `step("Construct canonical verification evidence")`
- `step("Reject stale or unsupported evidence")`
- `step("Replay the shipped artifact independently")`

The frozen helpers are `setup_fv2_fixture`, `check_fv2_gate`, and
`check_fv2_replay`. Until implemented, a helper must call `fail(...)`.

## Delivery waves and ownership

| Wave | Requirements | Owner and exclusive production scope | Executable evidence | Current status / blocker |
|---|---|---|---|---|
| 0 — truthful foundation | REQ-FV2-001, REQ-FV2-002, REQ-FV2-019, REQ-FV2-020 | assurance/profile and verification-report owners; `src/compiler/00.common/assurance/`, `src/compiler/90.tools/verify/` | FV2 system status/profile/failure matrix | **Implemented; executable admission blocked** |
| 1 — canonical VIR and typed MIR evidence | REQ-FV2-003, REQ-FV2-005, REQ-FV2-011, REQ-FV2-012, REQ-FV2-018 | frontend/MIR owners; `src/compiler/20.hir/`, `src/compiler/50.mir/` | focused MIR plus canonical-program/VIR cases | **Implemented; executable admission blocked** |
| 2 — exact proof frontend | REQ-FV2-004, REQ-FV2-006, REQ-FV2-007, REQ-FV2-008 | Lean/contract owners; MIR verification modules and `src/compiler/70.backend/backend/lean_*` | existing formal specs plus execution-linked adversarial system cases | **Implemented; Lean/tool execution blocked** |
| 3 — receipts, replay, compiler relation | REQ-FV2-009, REQ-FV2-010, REQ-FV2-013, REQ-FV2-016, REQ-FV2-017 | verifier/replay and selected backend owners; `src/compiler/90.tools/verify/`, selected `src/compiler/60.mir_opt/` and `70.backend/` files | forged/stale receipt, unsound transform, mutation, replay cases | **Implemented; external replay blocked** |
| 4 — SimpleOS vertical slice | REQ-FV2-014 | SimpleOS formal owners; bounded `src/verification/` and OS adapter scopes selected by reviewed design | capability/lifecycle/IPC/mapping/storage scenarios plus stable Lean entry points | **Implemented bounded slices; product proof execution blocked** |
| 5 — RISC-V product chain | REQ-FV2-015 | hardware formal owner; generated RTL/RVFI sidecars, manual Lean/BYL proof owners, formal wrappers | `check-riscv-formal-dual-track.shs`, strict SBY and mission-critical gates | **Blocked:** readiness cannot substitute for executed RVFI/SBY, oracle, refinement, equivalence, and artifact evidence |
| 6 — independent release closure | REQ-FV2-001, REQ-FV2-009, REQ-FV2-010, REQ-FV2-016, REQ-FV2-019, REQ-FV2-020 | release evidence owner; no production repairs in release | fresh Lean replay, independent checker, full regression and release gates | **Blocked:** predecessor waves and canonical self-hosted runtime are incomplete |

## NFR traceability

| NFR | Wave / owner | Required evidence | Status |
|---|---|---|---|
| NFR-FV2-001 reproducibility | 1, 3 / VIR and receipt owners | repeated semantic/certificate/receipt hashes from pinned inputs | Blocked |
| NFR-FV2-002 sound failure | all / each lane owner | malformed, stale, timeout, unknown, missing-tool negatives | Partial: MIR admission and unlowered consumers |
| NFR-FV2-003 bounded trust | 3, 6 / trust owner | complete transitive trust manifest and axiom audit | Blocked |
| NFR-FV2-004 incrementality | 1, 3 / cache owner | SymbolId/SCC invalidation and formatting-only reuse | Blocked |
| NFR-FV2-005 determinism | 1–3 / producer owners | byte-stable VIR, Lean IR, weave, receipts | Partial: MIR JSON only |
| NFR-FV2-006 performance | 3, 6 / tooling owner | warm latency, cache metrics, max RSS, no repeated scans | Blocked by unavailable self-hosted CLI |
| NFR-FV2-007 diagnostics | all / lane owners | source/SymbolId/value/effect/signal mapping | Partial: distinct MIR admission diagnostics |
| NFR-FV2-008 evolvability | all / interface owner | V1 migration and stale-cache tests | Names frozen; tests blocked |
| NFR-FV2-009 independence | 3, 5, 6 / replay and hardware owners | fresh Lean plus independent checker/oracle | Blocked |
| NFR-FV2-010 scalability | 3 / scheduler owner | bounded parallel DAG execution metrics | Blocked |

## Current-main acceptance inventory

- **Implemented, pending authoritative execution:** MIR probe variants and
  operand contracts; deterministic JSON; fail-closed shape diagnostics;
  optimizer, visitor, SSA, inline, DCE, transitive and compatibility liveness;
  focused unit spec and mirrored manual.
- **In progress:** explicit fail-closed coverage of every interpreter/backend.
  A wildcard that emits a NOP, comment, or successful artifact is a failure.
- **Not complete:** HIR-to-MIR probe insertion, admitted runtime lowering,
  zero-count manifest publication, typed VIR/contracts, trust/replay closure,
  compiler certificates, SimpleOS product refinement, RISC-V product proof,
  performance evidence, and final release verification.
- **Already integrated:** the first bounded MIR bridge commits were serialized,
  pushed, refetched, and proven reachable. This does not complete FV2.

## Test and documentation owners

| Artifact | Owner | State |
|---|---|---|
| `test/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.spl` | MIR evidence owner | Present; current focused foundation |
| `doc/06_spec/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.md` | MIR evidence owner + manual reviewer | Present; historical compatibility-liveness content from `8257fde9eb1` is accepted input |
| `test/03_system/compiler/formal_verification_2_0_spec.spl` | system-test owner | Present; 20 REQs, 10 NFRs, frozen steps/helpers, 81 examples |
| `doc/06_spec/03_system/compiler/formal_verification_2_0_spec.md` | docgen + merge owner | Present mirror; zero-stub regeneration blocked on Stage 4 runtime |
| `doc/03_plan/sys_test/simple_formal_verification_2_0.md` | system-test owner | Present in this lane; planning evidence only |
| research, requirements, architecture, detail design | research/design owners | Restored working-tree artifacts accepted by bounded high review; pending commit |

## Parallel lanes and reconciliation

These file sets are exclusive. A lane stops and asks the merge owner before
touching any file outside its set.

| Order | Lane | Exact allowed file set | Dependency | Required sidecar receipt | Acceptance |
|---:|---|---|---|---|---|
| 1 | A — MIR admission | `src/compiler/50.mir/mir_coverage_probe_admission.spl`; `test/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.spl`; `doc/06_spec/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.md` | frozen opcode shapes | commit/diff hash, commands, exit codes, changed scenarios, unresolved blockers | merge owner checks malformed-before-unlowered ordering and manual parity |
| 1 | B — native targets | `src/compiler/70.backend/backend/native/isel_x86_64.spl`; `src/compiler/70.backend/backend/native/isel_aarch64.spl`; `src/compiler/70.backend/backend/native/isel_riscv32.spl`; `src/compiler/70.backend/backend/native/isel_riscv64.spl`; `test/01_unit/compiler/backend/native_coverage_probe_rejection_spec.spl`; `doc/06_spec/01_unit/compiler/backend/native_coverage_probe_rejection_spec.md` | admission diagnostics only | same receipt fields plus all four target rows | merge owner rejects wildcard/NOP/comment handling |
| 1 | C — portable targets | `src/compiler/70.backend/backend/c_backend.spl`; `src/compiler/70.backend/backend/lua_backend.spl`; `src/compiler/70.backend/backend/wasm/wat_codegen.spl`; `src/compiler/70.backend/backend/vhdl_expr.spl`; `src/compiler/70.backend/backend/vhdl_backend.spl`; `src/compiler/70.backend/backend/common/gpu_codegen.spl`; `test/01_unit/compiler/backend/portable_coverage_probe_rejection_spec.spl`; `doc/06_spec/01_unit/compiler/backend/portable_coverage_probe_rejection_spec.md` | admission diagnostics only | same receipt fields plus C/Lua/WASM/VHDL/GPU matrix | merge owner confirms explicit lowering or pre-artifact rejection |
| 1 | D — interpreter/LLVM | `src/compiler/95.interp/mir_interpreter.spl`; `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`; `src/compiler/70.backend/backend/llvm_lib_translate.spl`; `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl`; `src/compiler/70.backend/backend/llvm_lib_backend.spl`; `test/01_unit/compiler/backend/interpreter_llvm_coverage_probe_rejection_spec.spl`; `doc/06_spec/01_unit/compiler/backend/interpreter_llvm_coverage_probe_rejection_spec.md` | admission diagnostics only | same receipt fields plus interpreter and both LLVM paths | merge owner confirms no backend success after unlowered probe |
| 2 | E — documentation | `.spipe/simple_formal_verification_2_0/state.md`; `doc/01_research/local/simple_formal_verification_2_0.md`; `doc/01_research/domain/simple_formal_verification_2_0.md`; `doc/02_requirements/feature/simple_formal_verification_2_0.md`; `doc/02_requirements/nfr/simple_formal_verification_2_0.md`; `doc/03_plan/agent_tasks/simple_formal_verification_2_0.md`; `doc/03_plan/sys_test/simple_formal_verification_2_0.md`; `doc/04_architecture/simple_formal_verification_2_0.md`; `doc/04_architecture/simple_formal_verification_2_0_tldr.md`; `doc/05_design/simple_formal_verification_2_0.md`; `doc/05_design/simple_formal_verification_2_0_tldr.md`; `doc/07_guide/compiler/lean_verification_workflow.md`; `doc/00_llm_process/feature_expert/formal_verification/skill.md`; `doc/00_llm_process/layer_expert/formal_verification/skill.md` | reconciled A–D statuses and frozen SPipe vocabulary | list of documents, REQ/NFR completeness audit, stale-claim audit | merge owner accepts links and blocker truthfulness after code lanes |
| 3 | F — verification | no production edits; reports/evidence only | merged A–E unchanged tree | exact command ledger, tool/binary hashes, exit codes, retained artifacts | independent highest-capability `$verify` review |

Lane E's file cell is exhaustive for this delivery: it owns the SPipe state,
every restored FV2 research/requirement/architecture/design document, both FV2
TLDR companions, both canonical plans, the Lean workflow guide, and both expert
skill documents. It does not own executable specs or generated manuals.

Merge order is A, then B/C/D in any order because their files are disjoint,
then E after the merge owner reconciles every sidecar receipt, then F. The
merge owner records accepted/rejected receipt IDs and reruns no criterion that
already passed on the unchanged tree. A sidecar result is advisory until the
merge owner accepts its diff, test truthfulness, exclusions, and blocker list.

**Independent high-review status: PASS (cycle 3, final).** The bounded reviewer
accepted the corrected interface mappings, current/proposed status, exhaustive
disjoint documentation ownership, executable command ledger, and Lean links.

## Blockers and stop criteria

- `bin/simple` and the canonical deployed self-hosted binary are absent in this
  worktree. A stale/noncanonical ELF failure or Rust-seed success is not PASS.
- Research, requirements, architecture, and design artifacts are committed.
  The system spec and manual mirror are present; authoritative SSpec/docgen
  execution remains blocked by the missing Stage 4 runtime.
- Each acceptance command runs at most once after PASS. Each gate has at most
  three fix/verify cycles; identical results stop and are reported.
- Final completion requires zero verification FAIL items, clean authoritative
  runtime gates, an intentional commit, serialized fetch/rebase/push without
  force or a branch, refetched reachability proof, clean detached worktree, and
  the required done marker. Incomplete predecessor gates remain unchecked.
