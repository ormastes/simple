# Feature Expert: Distributed Build and Fast Feedback

## Scope and status

This lane covers complete build-action identity, dependent artifact consumption, local and trusted remote scheduling, faster local/GitHub checks and push feedback, signed local build admission, Clang header policy/resources, CI, submodule pins and branch policy. It also composes the existing Simple Container/Orchestrator Pod/Job contracts with distributed workers across qualified host platforms. **In progress:** common contracts and local transitions are drafted but unverified; do not infer that worker dispatch, remote/container execution, Clang cache admission or GitHub build reuse has shipped.

## Entry documents

- Research: `doc/01_research/local/dist_build_scheduler_2026-09-25.md`, `doc/01_research/domain/dist_build_scheduler_fast_push_2026-09-25.md` and the extracted `simple_clang_header_cache_2026-09-25/` bundle.
- SPipe state: `.spipe/dist_build_scheduler/state.md` (feature/NFR selection and phase status are authoritative there).
- Plan and ownership: `doc/03_plan/compiler/build_system/dist_build_scheduler_2026-09-25.md`, `doc/03_plan/agent_tasks/dist_build_scheduler_2026-09-25.md`.
- Architecture and detail design: `doc/04_architecture/dist_build_scheduler.md`, `doc/05_design/dist_build_scheduler.md`.
- Existing cache knowledge: `doc/00_llm_process/feature_expert/cache_tiering/skill.md`; compiler and app layer routes remain applicable.

## Current code map and limits

| Path | Observed role |
|---|---|
| `src/app/build/targets/target_executor.spl`, `src/app/io/_CliCompile/native_dependency_inputs.spl` | A draft executable consumer/archive provider bridge now parses a dependency manifest and copies verified inputs. Link behavior is unverified on the current runtime; action digest and executor reuse remain unknown/disabled. |
| `src/app/build/targets/action_identity.spl`, `artifact_receipt.spl` | Existing typed action/dependency/closure identities and validation to extend, not replace with entry-only hashing. |
| `src/compiler/00.common/build_contract.spl`, `src/app/build/scheduler/`, `bin/simple_dist_build_parent` | Draft structural contracts plus parent-owned journal, remote attempt and source-level whole-graph runner. The runner reopens the owner after each attempt, resumes active work, requires one shared retained CAS root, and pins manifest bytes to an independently protected administrator `--graph-digest` before dispatch. The launch wrapper requires a SHA-256-pinned native controller; no qualified binary or real two-node PASS exists. |
| `src/app/build/scheduler/parent_link_template.spl`, `parent_link_resolution.spl` | A protected ordered cold-link template resolves accepted producer outputs through retained manifests and CAS into a complete link action/request only after publication. The staged graph transition and live compile/link execution are not wired or verified. |
| `src/app/build/scheduler/parent_staged_link.spl`, `parent_link_template_wire.spl`, `parent_staged_link_cli.spl` | Source-only two-phase controller binds producer manifest, exact template wire, link intent and worker-config bytes to an independently protected expected plan digest; checks closure before dispatch; derives the combined graph after accepted outputs. The CLI source loads pinned template and base request bytes through no-follow reads. No qualified native binary, administrator plan issuance, current-runtime PASS or live two-node evidence exists. |
| `src/app/build/scheduler/container_worker_admission.spl`, `src/app/ci/pipeline_runner.spl` | Draft app-level build-to-Pod eligibility and CI host/runtime gate. The Linux OCI provider is the only hosted container implementation; immutable build mounts, working directory, output publication and non-Linux provider qualification remain. |
| `src/app/build/gate_receipt.spl`, `signed_build_admission.spl` | Draft pure validators. Caller must verify signatures, protected policy, exact candidate, mandatory rows and artifact bytes; these files do not report GitHub statuses. |
| `src/app/build/signed_build_ci_observation.spl`, `signed_build_controller.spl` | Source-only current-identity precheck plus signature/private-artifact composition. The precheck compares caller-supplied PR, merge tree, protected identities, manifest and gate digest; it does not collect GitHub or gate observations. A base-owned collector and reporting required workflow are still missing. |
| `src/app/build/submodule_inventory.spl`, `config/build/submodule_inventory.sdn` | Selected gitlink inventory and structural checks. Automated trusted Git loading and clean remote canaries remain. |
| `src/app/cli/native_build_warm_receipt.spl`, `native_build_main.spl` | Exact final-artifact warm receipt and bounded parse/HIR shard warmers; neither is a distributed action scheduler. |
| `src/compiler/80.driver/cache/action_key.spl`, `cas_store.spl`, `remote/remote_client.spl` | Canonical key substrate, phase-one CAS and read-only fake-transport remote lookup; do not claim production remote execution from these. |
| `scripts/check/check-dist-issued-native.shs` | Linux-only isolated candidate builder for the restricted graph/staged parent and worker binaries. Requires a clean committed tree and admitted Stage 4 provenance; its receipt says `CANDIDATE_BUILT_UNQUALIFIED`, so live two-node and installation gates remain. |
| `src/app/build/clang_policy/native_ninja_controller.spl`, `native_ninja_graph.spl`, `native_rebuild_barrier.spl` | Source-only native Clang route checks an approved restricted Ninja graph and exact direct-object map under the build lock before stamp/object changes, invalidates prior output on rebuild, runs pinned Ninja and captures exact bytes. No production caller, real C/C++ PASS, complete toolchain closure or hostile-filesystem proof exists. |
| `config/check/must_check_gates.sdn`, `scripts/check/run-gate-tier.shs`, `scripts/check/check-push-must-pass.shs` | Existing gate registry/runner and 10-second per-ref blocking push budget; ordinary push reports default-skipped advisory count. |
| `scripts/hooks/`, `scripts/check/land.shs`, `.github/workflows/` | Worktree-aware hook and Git/JJ submission seams, signed receipt and GitHub checks. Required status and fork coverage must be checked against live current state before changes. |
| `.gitmodules`, `.spipe/policy/vcs.sdn` | Existing gitlinks and protected ref/work-branch policy. `HEAD` selects two gitlinks despite 18 declarations. Live main ruleset has an always-bypass role actor absent from tracked projection. A tracking branch is not the admitted submodule commit. |

## Invariants for future agents

1. User-selected final requirements and NFR targets govern implementation; a recommendation in an options file is not selection.
2. Action identity covers complete semantic inputs; attempt identity owns worker, retry, fence and scratch. Incomplete closure cannot yield a cache hit or accepted PASS. Only a validated broker accepts a result.
3. Keep one gate registry and current hook installer/dispatcher. Staged, outgoing committed and integration-candidate snapshots are different evidence scopes. Unknown/skipped required work is not PASS.
4. Keep the parent gitlink SHA authoritative and bind vendor exceptions to dependency identity. Do not fetch every optional example or move repository directories as a shortcut.
5. Preserve unrelated dirty files. In particular, `scripts/check/check-push-must-pass.shs` was dirty in another lane during research; recheck ownership before any edit.
6. Use the deployed pure-Simple runtime for production checks. The ZIP's twelve native counterexamples and 56 planned HC cases are not implementation verification.
7. A signed local build receipt can skip duplicate work only inside a GitHub job that still reports its required context. Missing/invalid/unsupported evidence falls back to the full remote build. A signature authenticates the claimant, not independent execution.
8. Distinguish physical host, execution OS/architecture, runtime isolation and compiler output target. A native-container request cannot become a plain process PASS. Portable Pod/Job syntax alone does not make images or OS enforcement portable. The current macOS bootstrap Cocoa owner failure and deployed test-runner crash block Simple acceptance checks; see `doc/08_tracking/bug/`.
