# Simple Formal Verification 2.0 — System Test Plan

**Status:** Implemented modern SSpec and manual mirrors; focused RVFI readiness
coverage prepared as `TEST_BLOCKED` pending an admitted Stage-4 CLI
**Date:** 2026-08-16
**Independent high-review:** **PASS (cycle 3, final)** for interface consistency,
status truthfulness, ownership, executable command closure, and Lean links.

## Canonical paths

- Executable: `test/03_system/compiler/formal_verification_2_0_spec.spl`
- Generated manual: `doc/06_spec/03_system/compiler/formal_verification_2_0_spec.md`
- Focused RVFI readiness executable:
  `test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl`
- Focused blocked manual mirror:
  `doc/06_spec/03_system/compiler/fv2_riscv_dual_track_readiness_spec.md`
- Focused implemented foundation:
  `test/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.spl`

The system spec must use built-in matchers and the frozen scenario flow:

1. `step("Audit the formal claim boundary")`
2. `step("Construct canonical verification evidence")`
3. `step("Reject stale or unsupported evidence")`
4. `step("Replay the shipped artifact independently")`

Frozen helpers are `setup_fv2_fixture`, `check_fv2_gate`, and
`check_fv2_replay`. An incomplete helper calls `fail(...)` and cannot silently
pass. Proof logs and receipts use `artifact`, `log`, `protocol`, or `exec`
captures.

## Scenario matrix

| Scenario | Requirements | Oracle | Current state |
|---|---|---|---|
| Truthful claim boundary | REQ-FV2-001, REQ-FV2-002, REQ-FV2-019, REQ-FV2-020; NFR-FV2-002 | model/source/backend/artifact statuses remain distinct; missing tool, timeout, unknown, and unsupported reject | Implemented; runtime blocked |
| Canonical evidence construction | REQ-FV2-003, REQ-FV2-005, REQ-FV2-010, REQ-FV2-011, REQ-FV2-012; NFR-FV2-001, NFR-FV2-005, NFR-FV2-008 | frozen identities bind expanded/woven source, typed VIR/MIR, effects, tools, and cache key deterministically | MIR JSON foundation only |
| Execution-linked exact proof | REQ-FV2-004, REQ-FV2-006, REQ-FV2-007, REQ-FV2-008, REQ-FV2-018; NFR-FV2-007 | deliberately wrong body, width/overflow/shift mismatch, unsupported node, vacuity, and disconnected result reject | Implemented; runtime blocked |
| Trust and compiler refinement | REQ-FV2-009, REQ-FV2-013, REQ-FV2-016, REQ-FV2-017; NFR-FV2-003, NFR-FV2-004 | hidden axiom, forged/stale receipt, unsound transform, mutation, and incompatible dynamic receipt reject | Implemented; external replay blocked |
| Incremental performance | REQ-FV2-010; NFR-FV2-006, NFR-FV2-010 | warm SymbolId/SCC checks retain timing, cache, scheduler, and max-RSS evidence without repeated full-tree scans | Blocked by unavailable self-hosted CLI |
| SimpleOS vertical slice | REQ-FV2-014, REQ-FV2-020; NFR-FV2-009, NFR-FV2-010 | stable manual Lean roots plus product-linked receipts survive adversarial lifecycle/interleaving/crash cases | Blocked; no current-main accepted slice |
| RISC-V dual track | REQ-FV2-015, REQ-FV2-019, REQ-FV2-020; NFR-FV2-002, NFR-FV2-009 | focused checker accepts exactly 21 canonical RVFI ports; missing extended ports/core reject; aggregate Lean/BYL and strict SBY gates both pass | Focused source/manual prepared; `TEST_BLOCKED`; readiness is not proof |
| Independent release replay | REQ-FV2-001, REQ-FV2-009, REQ-FV2-010, REQ-FV2-016, REQ-FV2-019, REQ-FV2-020; NFR-FV2-001, NFR-FV2-003, NFR-FV2-009 | fresh Lean and independent checker replay exact shipped bytes with closed trust | Blocked by all predecessors |

Every selected REQ must have a happy path, boundary case, and rejection path
before PASS. Current zero-case rows are failures, not exclusions.

## Per-ID executable traceability

In the trace table, `FV2SYS` labels
`test/03_system/compiler/formal_verification_2_0_spec.spl`; it is not a literal
shell command. `RVFIREADY` labels
`test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl`.
Every eventual system-test invocation uses the exact path shown
in the one-pass ledger below. Scenario names are
frozen acceptance names for its implementation. Unless a row names a narrower
reviewer, the reviewer is the independent highest-capability FV2 reviewer.
The blocker column records missing executable evidence, not missing source:
the capsule and scenarios are present, but no row is admitted until its named
runtime/tool command succeeds on the unchanged tree.

| ID | Implementation artifact | Exact happy / boundary / rejection oracle or test | Blocker | Prerequisite / executable resume command | Expected marker or artifact | Owner / reviewer |
|---|---|---|---|---|---|---|
| REQ-FV2-001 | `src/compiler/00.common/assurance/`; formal reports | FV2SYS `reports the four formal statuses`; `keeps backend_refined qualified`; `rejects model-only artifact_verified` | FV2SYS missing | Create the frozen system spec, then run its exact ledger command below | four distinct status rows; `artifact_verified=false` negative | assurance / independent FV2 |
| REQ-FV2-002 | assurance profile resolver/config | FV2SYS `resolves verified above critical`; `maps verified conservatively for V1`; `rejects unknown verified policy` | reviewed design accepted; implementation unconfirmed | `bin/simple check src/compiler/00.common/assurance`; then run the exact system-spec ledger command | versioned verified policy ID, no fifth V1 case | assurance / interface reviewer |
| REQ-FV2-003 | frontend expansion/weave and VIR producer | FV2SYS `binds one canonical program`; `changes hash for ordered advice`; `rejects proof/compiler hash drift` | canonical producer missing | `bin/simple check src/compiler/20.hir`; then run the exact system-spec ledger command | equal proof/compile semantic hash | VIR / independent FV2 |
| REQ-FV2-004 | execution-contract/obligation layer | FV2SYS `proves actual return transition`; `covers error result`; `rejects satisfiable postcondition disconnected from body` | execution-linked chain missing | `bin/simple test test/00_formal_verification/compiler/lean_workflow_spec.spl --mode=interpreter`; then run the exact system-spec ledger command | body-bound obligation hash; disconnected negative | contracts / Lean reviewer |
| REQ-FV2-005 | `VerificationIR v1` producer | FV2SYS `serializes complete typed VIR`; `preserves empty effect/call closure`; `rejects missing symbol/source identity` | V1 producer not accepted current-main | `bin/simple check src/compiler/50.mir`; then run the exact system-spec ledger command | deterministic VIR artifact and schema version | VIR / interface reviewer |
| REQ-FV2-006 | exact semantics classifiers/Lean lowering | FV2SYS `checks exact widths`; `checks overflow/shift boundary`; `rejects unsupported or implicit fallback` | broader exact-semantics closure missing | `bin/simple test test/00_formal_verification/compiler/lean_codegen_spec.spl --mode=interpreter`; then run the exact system-spec ledger command | exact BitVec widths; `unsupported` rejection | exact semantics / Lean reviewer |
| REQ-FV2-007 | typed Lean IR/emitter | FV2SYS `emits typed Lean deterministically`; `handles empty obligation set`; `rejects guessed type, placeholder _, or uninterpreted fallback` | typed FV2 IR chain incomplete | `bin/simple gen-lean verify` | Lean files with zero `sorry`/`admit` and no guessed nodes | Lean backend / Lean reviewer |
| REQ-FV2-008 | obligation generator/closure | FV2SYS `constructs full obligation DAG`; `accepts bounded leaf`; `rejects missing non-vacuity, frame, termination, or trust obligation` | full obligation kinds absent | `bin/simple verify check`; then run the exact system-spec ledger command | complete `ProofObligation v1` manifest | proof frontend / independent FV2 |
| REQ-FV2-009 | trust audit and replay tools | FV2SYS `accepts closed transitive trust`; `reports approved bounded TCB`; `rejects sorry/admit/hidden axiom/replay drift` | independent replay not current-main accepted | `bin/simple verify check` plus stable project `lake build` | zero forbidden axioms; fresh and independent receipts | trust/replay / independent FV2 |
| REQ-FV2-010 | receipt/cache-key layer | FV2SYS `binds all exact identities`; `invalidates one changed dependency`; `rejects forged/stale/artifact-drift receipt` | receipt closure incomplete | Produce proof artifacts, then run the exact system-spec ledger command | `ProofReceipt v1` and `VerificationCacheKey v1` hashes | evidence / interface reviewer |
| REQ-FV2-011 | macro/AOP weave manifest | FV2SYS `records ordered join points`; `handles no-advice program`; `rejects reordered/introduced-symbol drift or post-VIR transform` | canonical weave producer missing | `bin/simple check src/compiler`; then run the exact system-spec ledger command | `WeaveManifest v1`; changed-weave cache miss | AOP/VIR / interface reviewer |
| REQ-FV2-012 | typed effect and call closure | FV2SYS `propagates transitive typed effects`; `accepts pure leaf`; `rejects renamed/generated/indirect/external call without binding` | resolver-originated closure missing | `bin/simple check src/compiler/50.mir`; then run the exact system-spec ledger command | exact SymbolId closure; unresolved-call diagnostic | effects / compiler reviewer |
| REQ-FV2-013 | MIR/pass/backend validators | FV2SYS `accepts sound selected transform`; `maps boundary counterexample`; `rejects intentionally unsound transform or broken chain` | selected certificate pipeline missing | focused MIR spec, then `bin/simple check src/compiler` | checked `CompilerCertificate v1` chain | refinement / compiler reviewer |
| REQ-FV2-014 | stable SimpleOS manual proofs/adapters | FV2SYS `composes exact vertical slice`; `tests bounded lifecycle/crash edge`; `rejects missing/reordered/model-only subsystem receipt` | reviewed design accepted; product execution absent | `sh scripts/check/check-simpleos-critical-formal-proofs.shs` | stable Lean entry points plus source-bound receipts | SimpleOS formal / mission-critical reviewer |
| REQ-FV2-015 | RISC-V generated RVFI, manual proof, oracle/equivalence | FV2SYS bounded product checks + RVFIREADY complete 21-port manifest, aggregate proof-model gate, and strict SBY; rejects readiness-only evidence | focused source/manual prepared; admitted runtime/tools/artifacts unavailable | Run RVFIREADY once, then its aggregate and strict gates | both `STATUS: PASS` markers; `HardwareProofReceipt v1` remains broader closure | hardware formal / RTL reviewer |
| REQ-FV2-016 | mutation/vacuity/adversarial suite | FV2SYS `kills declared mutations`; `retains satisfiability/cover witness`; `rejects surviving property/implementation/evidence mutation` | complete matrix missing | Run the exact system-spec command followed by the formal ledger gates | mutation ledger with zero unexplained survivors | adversarial tests / independent FV2 |
| REQ-FV2-017 | dynamic composition receipt gate | FV2SYS `accepts compatible signed receipt`; `classifies explicit bounded TCB`; `rejects profile/interface/compiler-lineage/signature mismatch` | signed composition implementation unconfirmed | Run the exact system-spec ledger command after receipt support exists | compatible composition receipt or explicit bounded-TCB blocker | dynamic boundary / security reviewer |
| REQ-FV2-018 | existing proof syntax and external modules | FV2SYS `uses existing annotations/proof uses`; `handles external theorem dependency`; `rejects new grammar or unresolved theorem` | end-to-end emission/replay absent | `bin/simple test test/00_formal_verification/compiler/proof_reference_spec.spl --mode=interpreter` | deterministic external dependency in receipt | language/Lean / language reviewer |
| REQ-FV2-019 | every admission and target consumer | focused MIR spec + FV2SYS + RVFIREADY missing extended port, missing core, and deliberate-red mutation matrix | backend closure and admitted self-hosted run pending | Run the MIR spec and RVFIREADY once with the qualified CLI | distinct diagnostics; no readiness marker after incomplete input | all lane owners / merge owner |
| REQ-FV2-020 | ordered gate state machine/release | FV2SYS `advances gates in order`; `retains honest partial state`; `rejects skipped predecessor or premature verified release` | waves 0–6 incomplete | run full ledger below on unchanged tree | Gates 0–7 complete; `release_blockers=none` | merge/release / independent FV2 |
| NFR-FV2-001 | deterministic producers/receipts | FV2SYS `reproduces hashes twice`; `ignores formatting-only change`; `rejects source/tool/artifact drift` | canonical producers incomplete | repeat generation only after first run succeeds | identical semantic/certificate/receipt hashes | evidence / independent FV2 |
| NFR-FV2-002 | fail-closed reducers and wrappers | FV2SYS `accepts valid evidence`; `classifies supported blocker`; `rejects stale/contradictory/timeout/missing/unknown` | system matrix missing | Run the focused MIR command followed by the exact system-spec ledger command | nonzero rejection and retained diagnostic | every lane / merge owner |
| NFR-FV2-003 | `TrustManifest v1` | FV2SYS `lists closed trust`; `lists approved assumption boundary`; `rejects unnamed/unversioned/unattributed trust` | transitive trust audit incomplete | `bin/simple verify check` | complete trust manifest, zero hidden roots | trust / security reviewer |
| NFR-FV2-004 | SymbolId/SCC cache | FV2SYS `reuses unaffected SCC`; `invalidates changed dependency`; `rejects stale reverse-dependency result` | scheduler/cache integration missing | Run the exact system-spec ledger command with performance evidence enabled | cache hit/miss/invalidation receipt | cache / compiler reviewer |
| NFR-FV2-005 | all canonical emitters | FV2SYS `emits byte-stable evidence`; `handles stable empty sets`; `rejects ordering/nondeterministic drift` | only MIR JSON foundation present | run identical generation twice | byte-equal VIR/Lean/weave/receipt artifacts | producer owners / independent FV2 |
| NFR-FV2-006 | proof scheduler/tool runners | FV2SYS `meets warm budget`; `records zero-work warm case`; `fails on timeout/full-tree/per-obligation process regression` | canonical self-hosted CLI unavailable | Time the exact system-spec path from the ledger; do not substitute the label | elapsed/cache metrics and max RSS log | performance / performance reviewer |
| NFR-FV2-007 | diagnostic mappers | FV2SYS `maps counterexample to source/SymbolId`; `maps boundary value/effect/signal`; `rejects unmapped generic success/failure` | complete mapper absent | Run the exact system-spec ledger command and retain rejection diagnostics | typed diagnostic with source/effect/signal identity | diagnostics / independent FV2 |
| NFR-FV2-008 | ten frozen V1 schemas | FV2SYS `reads current V1`; `migrates explicit next version`; `rejects incompatible unversioned and stale-cache entry` | migration tests missing | Run the exact system-spec ledger command after migration scenarios exist | version/migration receipt and invalidation marker | interface / interface reviewer |
| NFR-FV2-009 | fresh Lean, independent checker, ISA oracle | FV2SYS `replays exact artifact independently`; `checks bounded supported oracle case`; `rejects checker/oracle/tool/artifact identity substitution` | independent tools/product evidence absent | stable `lake build`, dual-track, strict SBY | distinct checker/oracle hashes and accepted replay | replay/hardware / independent FV2 |
| NFR-FV2-010 | DAG scheduler | FV2SYS `runs independent SCCs in parallel`; `handles one-node DAG`; `rejects dependency-order violation, unbounded fanout, or lost result` | scheduler implementation/evidence missing | Run the exact system-spec ledger command with scheduler metrics enabled | bounded worker/DAG metrics with deterministic commit order | scheduler / concurrency reviewer |

## Existing focused MIR evidence

The focused unit spec currently checks deterministic serialization, operand
walking, mandatory observation, direct/transitive/compatibility liveness,
terminator liveness, malformed shape precedence, SSA/inlining rejection, and
explicit interpreter/LLVM rejection. Commit `8257fde9eb1` is accepted
historical input for compatibility-liveness test/manual wording; current-main
files are the executable authority.

Backend completion additionally requires each interpreter/target to lower an
admitted probe or reject before successful output. A wildcard comment, NOP, or
ignored instruction fails AC-3.

## One-pass acceptance command ledger

Run each command once on the final unchanged tree with the canonical Stage 4
self-hosted CLI. Record command, binary SHA-256, exit code, elapsed time, max
RSS, and retained-log hash. A seed or stale executable invalidates the ledger.

Focused and system evidence:

```sh
bin/simple test test/01_unit/compiler/mir/mir_coverage_opcode_admission_spec.spl --mode=interpreter
bin/simple test test/03_system/compiler/formal_verification_2_0_spec.spl --mode=interpreter
bin/simple test test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl --mode=interpreter --clean --timeout 900 --sequential
bin/simple spipe-docgen test/03_system/compiler/formal_verification_2_0_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/compiler/formal_verification_2_0_spec.spl
bin/simple lint test/03_system/compiler/formal_verification_2_0_spec.spl
bin/simple spipe-docgen test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl
bin/simple lint test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl
sh scripts/check/check-duplication.shs
```

Whole interpreter suite and compiler/library/tool-server checks:

```sh
bin/simple test --mode=interpreter
bin/simple check src/compiler
bin/simple check src/lib
bin/simple check src/app/mcp
bin/simple check src/app/simple_lsp_mcp
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
```

MCP/LSP native artifact smokes required because compiler language/backend
surfaces changed:

```sh
bin/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server
bin/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_lsp_mcp_server
sh scripts/check/check-bootstrap-essential-tools-smoke.shs bin/simple
```

Lean/formal and product gates:

```sh
bin/simple gen-lean verify
bin/simple verify check
sh scripts/check/check-lean-proofs.shs
sh scripts/check/check-riscv-formal-dual-track.shs
sh scripts/check/check-riscv-rtl-sby-proof.shs
sh scripts/check/check-simpleos-critical-formal-proofs.shs
sh scripts/check/check-simpleos-mission-critical-release.shs
```

If the mission-critical gate reports a host prerequisite blocker, record it and
run these diagnostics; they do not convert the release failure into PASS:

```sh
sh scripts/check/check-simpleos-mission-critical-prereqs.shs
sh scripts/setup/setup-simpleos-formal-env.shs --print-install
```

Working/staged audits, stub/layout checks, and final verification:

```sh
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
sh scripts/audit/numbered-artifact-guard.shs --working
sh scripts/audit/numbered-artifact-guard.shs --staged
test "$(find doc/06_spec -name '*_spec.spl' | wc -l)" -eq 0
! rg -n 'pass_todo|expect\(true\)\.to_equal\(true\)|assert\(true\)|# TODO|# FIXME' test/03_system/compiler/formal_verification_2_0_spec.spl src/compiler
```

After every required gate reports PASS, integration closure is executable as
one serialized transaction (with the detached worktree preserved):

```sh
flock /tmp/simple-main-restart12-push.lock sh -c 'set -eu; git add .spipe/simple_formal_verification_2_0/state.md doc/00_llm_process/feature_expert/formal_verification/skill.md doc/00_llm_process/layer_expert/formal_verification/skill.md doc/01_research/local/simple_formal_verification_2_0.md doc/01_research/domain/simple_formal_verification_2_0.md doc/02_requirements/feature/simple_formal_verification_2_0.md doc/02_requirements/nfr/simple_formal_verification_2_0.md doc/03_plan/agent_tasks/simple_formal_verification_2_0.md doc/03_plan/sys_test/simple_formal_verification_2_0.md doc/04_architecture/simple_formal_verification_2_0.md doc/04_architecture/simple_formal_verification_2_0_tldr.md doc/05_design/simple_formal_verification_2_0.md doc/05_design/simple_formal_verification_2_0_tldr.md doc/07_guide/compiler/lean_verification_workflow.md; git commit -m "docs: complete formal verification 2.0 plan"; env -u GH_TOKEN -u GITHUB_TOKEN git fetch origin main; git rebase origin/main; env -u GH_TOKEN -u GITHUB_TOKEN git push origin HEAD:main; env -u GH_TOKEN -u GITHUB_TOKEN git fetch origin main; git merge-base --is-ancestor HEAD origin/main; test -z "$(git status --porcelain)"; printf "%s PASS\n" "$(git rev-parse HEAD)" > /tmp/restart12-formal.done'
```

Expected terminal evidence is: focused/system PASS, docgen `0 stubs`, all seven
`sspec-maintain` component scores accepted, compiler/lib/MCP/LSP/native/bootstrap
gates exit 0, Lean has zero `sorry`/`admit`/untrusted project axioms,
dual-track and strict SBY print `STATUS: PASS`, mission-critical reports
`release_blockers=none`, audits are clean, and `$verify` reports `STATUS: PASS`.
Any missing tool, readiness-only result, timeout, stale mirror, nonzero exit, or
absent retained artifact remains a blocker.

## Manual-quality gate

The main manual must show the four frozen steps before folded implementation detail,
name both generated artifacts and durable proof entry points, expose every
named helper, contain zero placeholders, and remain readable without opening
the source. The focused RVFI manual must show its readiness, mutation,
missing-artifact, aggregate, and strict-proof steps while stating
`TEST_BLOCKED` until admitted docgen replaces the hand-maintained mirror.
`doc/06_spec` must contain zero executable `.spl` files. The merge
owner reviews all seven `sspec-maintain` component scores; the independent
final reviewer accepts traceability, exclusions, blocker truthfulness, and done
marks.
