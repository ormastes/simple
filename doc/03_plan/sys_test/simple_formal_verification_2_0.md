<!-- codex-design -->
# Simple Formal Verification 2.0 System Test Plan

**Status:** Implemented modern SSpec and manual mirror; runtime execution blocked
**Date:** 2026-08-14
**Recovery review:** **Source audit complete; overall acceptance WARN/blocked**
pending the canonical runtime, fresh reviewer reconciliation, and external
RV64 receipt execution.

Executable SPipe scenarios will live under `test/03_system/compiler/formal_verification_2_0_spec.spl`; the generated manual will mirror to `doc/06_spec/03_system/compiler/formal_verification_2_0_spec.md`. Scenario implementation begins with FV-0 and remains fail-fast until its oracle is real.

| Requirement | Scenario/oracle |
|---|---|
| REQ-FV2-001, REQ-FV2-002, REQ-FV2-019 | Status/profile matrix proves model-only, stale, timeout, unknown, missing-tool, and unsupported cases cannot produce verified release. |
| REQ-FV2-003, REQ-FV2-011 | Macro/aspect mutation changes exact weave manifest, semantic hash, closure, and cache result; proof and compiled VIR identities match. |
| REQ-FV2-004, REQ-FV2-008 | Deliberately wrong function body fails despite satisfiable postcondition; normal/error/frame/invariant/termination paths have real witnesses. |
| REQ-FV2-005, REQ-FV2-006, REQ-FV2-007 | Construct coverage matrix validates exact bit-vector overflow/shift/signed cases and rejects fallback/unknown Lean IR nodes. |
| REQ-FV2-009, REQ-FV2-010, REQ-FV2-016 | Hidden transitive axiom, `sorry`, native trust, forged receipt, stale artifact, and non-equivalent mutations turn the gate red. |
| REQ-FV2-012 | Aliased, indirect, method, generated, and renamed effectful calls remain visible in transitive typed effects. |
| REQ-FV2-013 | Sound compiler rewrite yields checked certificate; intentionally unsound rewrite yields mapped counterexample/failure. |
| REQ-FV2-014 | Kernel vertical slice preserves capability, lifecycle, IPC, mapping, and recovery invariants across adversarial interleavings/crashes. |
| REQ-FV2-015 | One RV32I family retires through generated RVFI, agrees with Sail, passes covers/mutations, and remains equivalent after accepted lowering. |
| REQ-FV2-017, REQ-FV2-018, REQ-FV2-020 | Plugin receipt/profile mismatch blocks composition; existing proof channels remain sufficient; delivery gates reject premature advancement. |

Only built-in matchers are used. No `pass_todo`, constant-true assertion, empty scenario, or comment-only oracle may satisfy a requirement. Captures use `artifact`, `log`, and `protocol` evidence for receipts, Lean/checker audits, counterexamples, RVFI traces, and equivalence reports.

## Open tooling performance blocker

`bin/simple check src/compiler/50.mir/verification_contract_bridge.spl` exceeded
both the default 60-second CPU guard and an explicit 120-second wall-clock
guard on 2026-08-12 without producing a source diagnostic. The available
binary also identifies itself as the Rust bootstrap seed, so this is not
release evidence. Acceptance: the pure-Simple self-hosted checker must complete
this focused file in at most 30 seconds warm, report max RSS, and return a
truthful nonzero status on timeout or compilation failure.
The same bounded diagnostic against
`src/compiler/90.tools/verify/replay_runner.spl` exited 124 after 35 seconds on
2026-08-12 without a source diagnostic; it is bootstrap-only evidence and was
not retried.

Only these four flow anchors are frozen. Scenario-local `step(...)` labels may
describe individual checks and are not additional frozen interface names.

Only these four flow anchors are frozen. Scenario-local `step(...)` labels may
describe individual checks and are not additional frozen interface names.

## Scenario matrix

| Scenario | Requirements | Oracle | Current state |
|---|---|---|---|
| Truthful claim boundary | REQ-FV2-001, REQ-FV2-002, REQ-FV2-019, REQ-FV2-020; NFR-FV2-002 | model/source/backend/artifact statuses remain distinct; missing tool, timeout, unknown, and unsupported reject | Implemented; runtime blocked |
| Canonical evidence construction | REQ-FV2-003, REQ-FV2-005, REQ-FV2-010, REQ-FV2-011, REQ-FV2-012; NFR-FV2-001, NFR-FV2-005, NFR-FV2-008 | frozen identities bind expanded/woven source, typed VIR/MIR, effects, tools, and cache key deterministically | VIR closure is hardened; Gate 3 deliberately fails until the compiler owns weave-manifest production |
| Execution-linked exact proof | REQ-FV2-004, REQ-FV2-006, REQ-FV2-007, REQ-FV2-008, REQ-FV2-018; NFR-FV2-007 | deliberately wrong body, width/overflow/shift mismatch, unsupported node, vacuity, and disconnected result reject | Implemented; runtime blocked |
| Trust and compiler refinement | REQ-FV2-009, REQ-FV2-013, REQ-FV2-016, REQ-FV2-017; NFR-FV2-003, NFR-FV2-004 | hidden axiom, forged/stale receipt, unsound transform, mutation, and incompatible dynamic receipt reject | Hash-only VC replay promotion is disabled; approved replay authority/execution remains blocked |
| Incremental performance | REQ-FV2-010; NFR-FV2-006, NFR-FV2-010 | warm SymbolId/SCC checks retain timing, cache, scheduler, and max-RSS evidence without repeated full-tree scans | Recursive work identities and measured-envelope validation implemented; scalar execution remains fail-closed until the task facade supplies real metrics |
| SimpleOS vertical slice | REQ-FV2-014, REQ-FV2-020; NFR-FV2-009, NFR-FV2-010 | stable manual Lean roots plus product-linked receipts survive adversarial lifecycle/interleaving/crash cases | Explicitly excluded from this delivery; its scenarios are regression-only and cannot prove Wave 4 closure |
| RISC-V dual track | REQ-FV2-015, REQ-FV2-020; NFR-FV2-009 | exact RVFI/SBY proof, independent ISA oracle, refinement/equivalence, and artifact identities agree | RV32 aggregation/RVFI/SBY and RV64 fail-closed authority runner present; canonical wrappers and exact proof/netlist/Linux/oracle inputs remain blocked |
| Independent release replay | REQ-FV2-001, REQ-FV2-009, REQ-FV2-010, REQ-FV2-016, REQ-FV2-019, REQ-FV2-020; NFR-FV2-001, NFR-FV2-003, NFR-FV2-009 | fresh Lean and independent checker replay exact shipped bytes with closed trust | Caller assembly is fail-closed; no accepting finalizer exists until runner-owned checker, gate-producer, and signer-policy authority is available |

| Requirement | Executable cases | Coverage |
|---|---:|---|
| REQ-FV2-001 | 3 | Foundation full |
| REQ-FV2-002 | 3 | Foundation full |
| REQ-FV2-003 | 0 | Missing: canonical macro-to-VIR production path |
| REQ-FV2-004 | 4 | Source contract retention, actual-call/non-vacuity roots, proof/source identity, typed authorities, direct-recursion termination, pure invariant/frame emission, and actual-function pre/post/frame proofs for the homogeneous straight-line global-state subset; explicit state-bound invariants, heap, and general CFG remain pending |
| REQ-FV2-005 | 0 | Partial unit coverage only; broader construct/source-map/call closure remains incomplete |
| REQ-FV2-006 | 6 | VIR and canonical MIR-to-Lean paths use exact BitVec widths and preserve Result payload/variant identity; float, pointer, signedness-ambiguous division/shift, checked arithmetic, heap, cast, and undeclared aggregate semantics fail closed |
| REQ-FV2-007 | 3 | Typed Lean IR foundation |
| REQ-FV2-008 | 3 | Canonical MIR foundation: deterministic thirteen-kind DAG, exact function authorities, acyclic-CFG termination, pure-leaf module-call composition, and an all-thirteen replay-bound discharge validator capped at `model_proven`. `ResolvedDirectCallManifestV1`/`ResolvedCanonicalModuleClosureV2` now bind legacy textual direct-call sites to exact resolver SymbolIds/signature/body/module snapshots without trusting name lookup. Cyclic loop measures, transitive/effectful SCC composition, canonical resolver production, and executed proof discharge remain missing. |
| REQ-FV2-009 | 4 | Trust parser/generator foundation, exact-root collision rejection, pinned independent exporter/checker provisioning, and one executed exact-root independent replay; six Gate 4 roots remain rejected at the closed nanoda Nat-literal boundary |
| REQ-FV2-010 | 6 | Receipt/cache/trust identity plus SymbolId/SCC scheduling and reverse-dependency invalidation |
| REQ-FV2-011 | 3 | Weave identity/certificate foundation; macro production bridge missing |
| REQ-FV2-012 | 5 | Typed transitive closure plus canonical MIR-derived global manifests, deterministic module-VIR closure identity, caller-effect mismatch rejection, generated-helper propagation, and unresolved pointer/indirect/external gates. V2 effect closure consumes `ResolvedDirectCallManifestV1` bindings rather than text-name-to-SymbolId lookup; missing/stale call bindings fail. Heap regions, canonical resolver production, and indirect dispatch remain pending. |
| REQ-FV2-013 | 4 | Proved straight-line DCE validator plus Result logical/tagged-ABI observation certificates bound to runtime artifact/proof/audit identities; full MIR and backend edges remain missing |
| REQ-FV2-014 | 22 | Seven implementation-linked slices have typed proof/replay-bound source-promotion paths. The green-channel close/drain root passed executed independent replay; capability, scheduler, memory, lifecycle, process-queue, and DBFS roots remain replay-rejected on closed nanoda `#ELN` support. Raw audit inputs remain `model_proven`; no partial matrix can promote Gate 4. Orphan adoption, general map/unmap, multi-record recovery, and concurrent interleavings also remain pending. |
| REQ-FV2-015 | 4 | Typed ADD provider/trap/retirement composition emits strict VHDL, captures dispatch source evidence, derives hashed RVFI, and rejects the disabled LSU. Constructed job receipts remain `specified`; exact executed SBY proof/cover/killed-mutant evidence can become `model_proven`. The GHDL/Yosys equivalence runner binds module, RTL, synthesized JSON netlist, proof log, tools, and synthesis policy and caps combined evidence at `backend_refined`. The pinned Sail runner compiles exact ADD opcode `002081b3`, requires the RV32 model to produce x3=12, binds all oracle/probe/trace identities, and caps the bounded witness at `model_proven`; it currently reports blocked because the pinned simulator/config are absent. The pure-Simple end-to-end gate also rejects the current Rust seed, so production ADD jobs/equivalence have not executed. Final artifact closure remains missing. |
| REQ-FV2-016 | 0 | Missing: complete semantic mutation/cover suite |
| REQ-FV2-017 | 3 | Signed receipt/interface/profile/compiler-lineage/composition gate and explicit bounded-TCB classification |
| REQ-FV2-018 | 1 | Partial: retained `proof uses` expands deterministically over all thirteen canonical VC identities, and unit evidence requires each generated receipt to include its exact external theorem dependency. Executed Lean emission/audit/replay remains missing. |
| REQ-FV2-019 | 3 | Typed/system fail-closed reducer plus a one-bundle CLI with repository-pinned signer policy, SHA-256 evidence identities, signed-bundle binding, pure-Simple Ed25519 verification, strict SDN parsing, and fixed-root receipt materialization. Unit cases cover admission, unknown-field injection, duplicate signer identity, payload drift, tampered signatures, wrong-key policy, missing receipt files, and changed receipt content. Executed self-hosted test evidence remains pending. |
| REQ-FV2-020 | 7 | Frozen eight-gate state machine accepts honest partial progress, rejects skipped predecessors, and requires the verified-release decision only after all gates pass. CLI admission recomputes the canonical gate-manifest hash bound into signed evidence, including each receipt/status/diagnostic. Gates 0–7 have typed collectors; executed external/product evidence and final self-hosted verification remain pending. |
| REQ-FV2-001, REQ-FV2-003 | unit | Typed Gate 0 collector accepts unique roots only when exact SHA-256 proof receipts bind a closed transitive axiom audit and accepted fresh/independent replay of the same artifact; weak hashes, `sorryAx`, replay drift, and duplicate roots fail without passing receipt material. |
| REQ-FV2-005, REQ-FV2-006 | unit | Typed Gate 1 collector recomputes canonical VIR function/module SHA-256 identities, accepts exact reachable types only, and requires five ordered executed check receipts bound to the same VIR. Forged provenance, unsupported/abstract types, stale/reordered/missing checks, retained-output absence, and failed outcomes block the gate. |
| REQ-FV2-008, REQ-FV2-010 | unit | Typed Gate 2 collector binds executed woven→VIR construction and a gap-free sequence of independently checked compiler certificates ending at the exact artifact. Woven drift, chain gaps/reordering, validator substitution, timeout/output absence, and wrong final artifact fail closed. |
| REQ-FV2-009 | unit | Typed Gate 3 collector binds exact macro/weave provenance, pointcut SymbolIds, introduced-symbol closure, advice certificates, materialized Gate 0 proof dependencies, and the post-proof transformation lock. Missing symbols/certificates/proofs, behavior-changing advice, provenance drift, or unlock attempts fail. |
| REQ-FV2-014, REQ-FV2-020 | unit | Typed Gate 4 collector requires seven ordered `source_refined` SimpleOS subsystem receipts and independently rechecks their exact SHA-256 source/model identity, proof/cache/trust/audit/replay closure. Missing, reordered, model-only, stale, artifact-drifted, or duplicate evidence fails closed. |
| REQ-FV2-015, REQ-FV2-020 | unit | Typed Gate 5 collector composes exact generated RV32 ADD SBY proof/cover/mutation, an independently checked HWIR-to-RTL certificate, RTL-netlist equivalence, and pinned Sail witness evidence. Status substitution, scope gaps, product drift, wrong compiler edges, weak/missing material, or netlist absence fails closed. |
| REQ-FV2-015, REQ-FV2-020 | unit | Typed Gate 6 collector binds shared-XLEN, privilege/CSR, MMU, precise trap/interrupt, synthesis-equivalence, Linux-boot, and ACT checks to one RV64 HWIR/RTL/netlist/image/platform/assumption identity. Formal proof, refinement certificate, and executed-validation classes cannot substitute for one another. |
| REQ-FV2-019, REQ-FV2-020 | unit | Typed Gate 7 collector seals a unique materialized `artifact_verified` proof/compiler/trust/replay/mutation/non-vacuity closure before manifest signing. The CLI rehashes the fixed-root deployed artifact bytes and compares them with both signed artifact identities before signer or receipt admission. |

Zero-case rows are release failures, not exclusions or implied coverage.

## Execution and evidence commands

| ID | Implementation artifact | Exact happy / boundary / rejection oracle or test | Blocker | Prerequisite / executable resume command | Expected marker or artifact | Owner / reviewer |
|---|---|---|---|---|---|---|
| REQ-FV2-001 | `src/compiler/00.common/assurance/`; formal reports | FV2SYS `reports the four formal statuses`; `keeps backend_refined qualified`; `rejects model-only artifact_verified` | executable system spec present; canonical runtime missing | Run its exact ledger command below | four distinct status rows; `artifact_verified=false` negative | assurance / independent FV2 |
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
| NFR-FV2-005 | all canonical emitters | FV2SYS `emits byte-stable evidence`; `handles stable empty sets`; `rejects ordering/nondeterministic drift` | producers present; unchanged-tree repeat evidence blocked | run identical generation twice | byte-equal VIR/Lean/weave/receipt artifacts | producer owners / independent FV2 |
| NFR-FV2-006 | proof scheduler/tool runners | FV2SYS `meets warm budget`; `records zero-work warm case`; `fails on timeout/full-tree/per-obligation process regression` | canonical self-hosted CLI unavailable | Time the exact system-spec path from the ledger; do not substitute the label | elapsed/cache metrics and max RSS log | performance / performance reviewer |
| NFR-FV2-007 | diagnostic mappers | FV2SYS `maps counterexample to source/SymbolId`; `maps boundary value/effect/signal`; `rejects unmapped generic success/failure` | complete mapper absent | Run the exact system-spec ledger command and retain rejection diagnostics | typed diagnostic with source/effect/signal identity | diagnostics / independent FV2 |
| NFR-FV2-008 | frozen Policy V1→V2 boundary plus ten frozen V1 schemas | focused migration spec + FV2SYS `reads current V1`; `migrates explicit next version`; `rejects incompatible unversioned and stale-cache entry` | typed migration receipt/spec implemented; runtime blocked | Run the focused migration spec and exact system-spec ledger command | version/migration receipt and invalidation marker | interface / interface reviewer |
| NFR-FV2-009 | fresh Lean, independent checker, ISA oracle | FV2SYS `replays exact artifact independently`; `checks bounded supported oracle case`; `rejects checker/oracle/tool/artifact identity substitution` | independent tools/product evidence absent | stable `lake build`, dual-track, strict SBY | distinct checker/oracle hashes and accepted replay | replay/hardware / independent FV2 |
| NFR-FV2-010 | DAG scheduler | focused proof-DAG/performance specs + FV2SYS `runs independent SCCs in parallel`; `handles one-node DAG`; `rejects dependency-order violation, unbounded fanout, or lost result` | bounded work planning, recursive dependency identity, and deterministic measured-result commit validation implemented; scalar worker execution blocked | Run the focused specs and exact system-spec ledger command with scheduler metrics enabled | bounded worker/DAG metrics with deterministic commit order | scheduler / concurrency reviewer |

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
bin/simple test test/01_unit/compiler/assurance/schema_migration_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/assurance/proof_dag_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/assurance/proof_performance_evidence_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/verify/fv2_wave6_orchestrator_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/verify/riscv_add_formal_bundle_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/verify/rv64_product_evidence_runner_spec.spl --mode=interpreter
bin/simple test test/03_system/compiler/formal_verification_2_0_spec.spl --mode=interpreter
bin/simple spipe-docgen test/03_system/compiler/formal_verification_2_0_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/compiler/formal_verification_2_0_spec.spl
bin/simple lint test/03_system/compiler/formal_verification_2_0_spec.spl
bin/simple spipe-docgen test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl --output doc/06_spec --no-index
bin/simple sspec-maintain scan test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl
bin/simple lint test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl
sh scripts/check/check-duplication.shs
sh scripts/rtl/check-fv2-rv32-add-end-to-end.shs
sh scripts/rtl/run-riscv-scalar-runtime-pipeline-v9-formal.shs --self-test
```

Lean/RISC-V product acceptance remains separate:

```sh
(cd src/verification/kernel_capabilities && lake build)
sh scripts/check/check-riscv-formal-dual-track.shs
sh scripts/check/check-riscv-rtl-sby-proof.shs
sh scripts/check/check-simpleos-mission-critical-release.shs
```

The capability-rights Lean build must report
`KernelCapabilities.rights_allow9_sound` with only `propext` and `Quot.sound`
(and may report `Classical.choice` for other roots). Any generated
`_native.bv_decide.ax_*`, `Lean.trustCompiler`, `sorryAx`, or project axiom
keeps the source-refinement receipt failed.

A missing tool, timeout, readiness-only result, or placeholder-rejected result
is retained blocker evidence, never a substitute PASS.

## Manual rendering policy

Foundation scenarios are visible. Helper construction functions and complete
executable source may be folded. Proof logs, receipts, counterexamples, RVFI
traces, and equivalence reports use linked `log`, `artifact`, or `protocol`
evidence rather than screenshots. The current manual mirror is explicitly
provisional until zero-stub doc generation runs on the pure-Simple toolchain.
