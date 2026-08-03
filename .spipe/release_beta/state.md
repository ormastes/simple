# Feature: release_beta

## Raw Request
Read `doc/03_plan/infra/agent_sessions/release_beta.md`, continue the main-working-copy lane, and complete `$sp_dev complete release_beta.md`.

## Task Type
todo

## Refined Goal
Produce and verify the next Simple 1.0.0 beta release from the main working copy with reproducible strict bootstrap artifacts, production-ready release checkers and GitHub Actions, and all supported non-macOS platform packages succeeding without unresolved stubs or unbounded memory/performance behavior.

## Acceptance Criteria
- AC-1: A fresh strict Linux stage2→stage3→stage4/full-CLI bootstrap from the main working copy completes with `SIMPLE_NO_STUB_FALLBACK=1`, and every stage log reports zero failed compilations and no unresolved generated stubs.
- AC-2: The exact fresh Stage 4 full CLI passes `scripts/check/check-bootstrap-essential-tools-smoke.shs`, including test-runner, lint, duplicate-check, and aggregate PASS markers.
- AC-3: The cyclic/transitive facade-glob resolution regression has focused executable coverage proving mixed facade modules expose required imported names and cycle traversal is bounded; retained measurements show no multi-GiB runaway and no material regression versus the accepted baseline.
- AC-4: Release payload, SimpleOS scenario, and MCP/LSP release checker entrypoints invoked by `.github/workflows/release.yml` exist, fail closed on invalid fixtures, and pass their focused contract tests.
- AC-5: The release workflow builds and validates every supported non-macOS release target declared by the repository, with platform-specific bootstrap/package checks passing; macOS is explicitly excluded only as stated by the lane goal.
- AC-6: The local workflow-equivalent release process completes for the next `1.0.0` beta version, producing validated compiler/runtime/package artifacts with notices, safe archive layout, checksums, and correct MCP package identity.
- AC-7: The GitHub Actions release workflow is syntactically valid, references only existing commands/files/artifacts, has correct dependency and upload/download wiring, and a real repository workflow run succeeds before the release is declared complete.
- AC-8: Compiler/core/lib and MCP/LSP verification gates required by `AGENTS.md` pass once, including direct env/runtime guards, core checks, MCP stdio integration, and native MCP/LSP package smoke when the release/package path changed.
- AC-9: Release-bound test evidence passes once on the exact fresh pure-Simple CLI: `bin/simple test test --whole --mode=interpreter`, with no placeholder SPipe assertions, zero executable `*_spec.spl` files under `doc/06_spec`, and generated/manual release scenario documentation readable as an operator manual.
- AC-10: Research, requirements, architecture, detail design, system-test plan/spec/manual, agent-task plan, affected guides, workflow/process instructions, changelog, and release handoff are current and trace every AC to implementation and executable evidence.
- AC-11: Production readiness verification reports `STATUS: PASS`; only then is the requested beta version committed and tagged, and pushing the main bookmark/tag occurs only after explicit user authorization.

## Scope Exclusions
- macOS bootstrap/package execution is excluded by the original lane goal; workflow syntax and artifact wiring for any retained macOS configuration still must not be broken.
- Pushing commits, tags, packages, or workflow dispatches without explicit user authorization is excluded.
- Unrelated dirty main-working-copy files owned by concurrent lanes are excluded and must be preserved.

## Cooperative Review
- Lower-model sidecars: N/A in the current runtime because only normal frontier Codex agents are exposed; broad findings require final normal/highest-capability review by `/root`.
- Merge owner: `/root` in the main working copy.
- Final reviewer: `/root` after all executable evidence is retained; no generated done marks or broad exclusions are accepted without direct review.
- Shared interfaces: `release_checker_contract`, `strict_bootstrap_candidate`, `release_workflow_platform_matrix`, `release_artifact_receipt`.
- Manual flow helpers: `step("Build the strict bootstrap chain")`, `step("Qualify the fresh full CLI")`, `step("Validate release payloads and tool servers")`, `step("Audit the platform workflow matrix")`, `step("Record the releasable beta handoff")`.
- Setup/checker helpers: existing `bootstrap-from-scratch.sh`, `check-bootstrap-essential-tools-smoke.shs`, `release_checker_contract_test.shs`, `check_release_payload.shs`, `check-mcp-release-assets.shs`; new helpers, if required, must fail closed.
- Fail-fast placeholders: `assert(false)` or `fail(...)`; `pass_todo`, empty scenarios, and tautological expectations are forbidden.
- Generated-manual review owner: `/root`.

## Phase
spec-in-progress

## Log
- dev: Created state file with 11 acceptance criteria (type: todo).
- dev: Runtime-boundary decision: `runtime_need=none`, `facade_checked=not-applicable`, `chosen_path=reuse-existing-compiler-and-release-facades`, `rejected_shortcuts=Rust-seed release evidence; stub fallback; raw runtime aliases; fixture-only workflow passes`.

## Research Summary

### Existing Code
- `scripts/bootstrap/bootstrap-from-scratch.sh:1135-1850` owns strict Stages 2-6, full-CLI admission, MCP smoke, deploy rollback, and whole tests.
- `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:900-1010` owns facade-glob traversal; the main working copy now memoizes cyclic expansion.
- `.github/workflows/release.yml:65-1205` declares platform builds, packages, artifact transfer, and release publication.
- `test/01_unit/scripts/release_checker_contract_test.shs:1-93` provides focused fail-closed checker fixtures.
- `scripts/check_release_payload.shs` and `scripts/check-mcp-release-assets.shs` are reusable package validators.

### Reusable Modules
- Strict bootstrap + Stage 4 essential-tools and Stage 5 MCP handshake gates.
- Existing payload/archive/font, executable-budget, SimpleOS, and MCP checker owners.
- GitHub artifact `needs`/upload/download model and repository-scoped `GITHUB_TOKEN` release authentication.

### Domain Notes
- Required artifact uploads must fail on missing files; caches are not release artifact evidence.
- The current workflow diff's source-only fallback for a missing executable full package conflicts with fail-closed release semantics.
- Latest remote Release run `30682874548` failed: Windows checkout, FreeBSD x86 cross-build, and SimpleOS full-kernel jobs failed; downstream full-package, whole-test, release, and GHCR jobs were skipped.

### Open Questions
- NONE. User selected Feature B and NFR B.

<!-- sdn-diagram:id=release_beta.research -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=release_beta.research hash=sha256:auto render=ascii
@layout dag
@direction LR
MainWC -> StrictBootstrap
StrictBootstrap -> FreshFullCLI
FreshFullCLI -> ReleaseCheckers
ReleaseCheckers -> PlatformArtifacts
PlatformArtifacts -> GitHubRelease
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=release_beta.research hash=sha256:auto
MainWC -> StrictBootstrap -> FreshFullCLI -> ReleaseCheckers -> PlatformArtifacts -> GitHubRelease
```

</details>
<!-- sdn-diagram:end -->

## Requirements
- REQ-1 (AC-1, AC-2): Produce a strict fresh Stage 4 full CLI and qualify its essential commands — area: `scripts/bootstrap/`, `src/compiler/`.
- REQ-2 (AC-3): Bound transitive facade-glob resolution while preserving mixed-facade names — area: `src/compiler/20.hir/`.
- REQ-3 (AC-4): Keep all release checker entrypoints tracked and fail closed — area: `scripts/`, `test/01_unit/scripts/`.
- REQ-4 (AC-5, AC-6): Validate every selected non-macOS platform package and its payload identity — area: `.github/workflows/release.yml`, packaging scripts.
- REQ-5 (AC-7): Prove artifact dependencies and a real successful GitHub release workflow run — area: `.github/workflows/release.yml`.
- REQ-6 (AC-8, AC-9): Pass core, MCP/LSP, whole-test, runtime-boundary, and SPipe evidence gates on the fresh CLI — area: `scripts/check/`, `test/`.
- REQ-7 (AC-10, AC-11): Keep design/process/release docs current and require verify PASS before commit/tag/push — area: `doc/`, `.spipe/`, release metadata.

## Log
- research: Found 6 reusable owners, 5 active gaps, and 7 mapped requirements; created local/domain research and requirement options.
- research: Audited remote run `30682874548`; AC-5..AC-7 are currently contradicted by authoritative GitHub Actions results.
- blocked: Requirement selection requested for three consecutive goal turns; architecture cannot begin until the user selects Feature A/B/C and NFR A/B/C. Recommended selection remains B/B because it matches the recorded lane goal.
- requirements: User selected Feature B and NFR B; wrote final requirement documents and deleted the unselected option documents.

## Architecture

### Module Plan
| Module | Path | Role | Change |
|---|---|---|---|
| HIR facade traversal | `src/compiler/20.hir/hir_lowering/{types.spl,_Items/module_lowering.spl}` | Bounded mixed-facade symbol reachability | Modified |
| Strict bootstrap | `scripts/bootstrap/bootstrap-from-scratch.sh` | Produce and admit Stages 2–5 | Existing |
| Release checkers | `scripts/check*_release*.shs`, `scripts/check/check-bootstrap-essential-tools-smoke.shs` | Fail-closed candidate/payload checks | Existing/modified as findings require |
| Workflow matrix | `.github/workflows/release.yml` | Platform builds, artifact aggregation, publication | Modified |
| Release scenario | `test/03_system/app/release/release_beta_spec.spl` | Operator flow and AC traceability | New |
| Scenario manual | `doc/06_spec/03_system/app/release/release_beta_spec.md` | Generated operator manual | New |

### Dependency Map
- HIR traversal -> parser module surfaces and symbol table.
- Strict bootstrap -> HIR traversal -> fresh Stage 4 CLI.
- Release scenario -> existing checker scripts and retained receipts.
- Workflow matrix -> strict candidate/platform producers -> artifact receipt -> GitHub release.
- No circular layer dependencies.

### Decisions
- Stage 4 alone qualifies release commands; seed/Stage 2 are diagnostic.
- Required executable roles fail rather than silently becoming source-only.
- Per-root shallowest-depth memo bounds facade cycles without reducing depth-capped reachability.
- Existing checker/QEMU owners remain canonical.

### Public API
- `strict_bootstrap_candidate(source_revision) -> Stage4CandidateReceipt`
- `release_checker_contract(candidate, artifact) -> CheckReceipt`
- `release_workflow_platform_matrix(version) -> [PlatformArtifactReceipt]`
- `release_artifact_receipt(version, candidates, checks) -> ReleaseReceipt`

<!-- sdn-diagram:id=release_beta.state_arch -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=release_beta.state_arch hash=sha256:auto render=ascii
@layout dag
@direction LR
CompilerFix -> StrictBootstrap
StrictBootstrap -> FreshCLI
FreshCLI -> Checkers
FreshCLI -> PlatformMatrix
Checkers -> Receipt
PlatformMatrix -> Receipt
Receipt -> Publication
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=release_beta.state_arch hash=sha256:auto
CompilerFix -> StrictBootstrap -> FreshCLI -> Checkers -------+
                                      +-----> PlatformMatrix -+-> Receipt -> Publication
```

</details>
<!-- sdn-diagram:end -->

### Requirement Coverage
- REQ-1 -> Strict bootstrap + qualification.
- REQ-2 -> HIR facade traversal.
- REQ-3 -> Release checkers + scenario.
- REQ-4/5 -> Workflow matrix + artifact receipt.
- REQ-6 -> Fresh CLI verification gates.
- REQ-7 -> SPipe/manual/release handoff.

## Log
- arch: Designed 6 modules and 4 decisions with no circular dependencies.

## Specs

### Spec Files
- `test/03_system/app/release/feature/release_beta_spec.spl` — 6 scenarios covering AC-1..AC-11 through real checker and receipt execution.

### Generated Manuals
- `doc/06_spec/03_system/app/release/feature/release_beta_spec.md` — manual-first mirror created; fresh Stage 4 docgen remains required before `spec-done`.

### Manual Shape
| Scenario | Visibility | Capture | Setup |
|---|---|---|---|
| receipt contract calibration | inline | exec | root setup |
| strict bootstrap chain | show | log | previous calibration |
| full CLI and release checkers | show | exec | direct |
| platform workflow matrix | show | log | direct |
| GitHub release workflow | show | protocol | direct |
| absent evidence directory | folded | exec | direct |

### AC Coverage Matrix
| AC | Scenario | Current status |
|---|---|---|
| AC-1/2/3 | strict bootstrap chain | Red: readiness checker/evidence incomplete |
| AC-4/6 | full CLI and release checkers | Red |
| AC-5 | platform workflow matrix | Red |
| AC-7 | GitHub release workflow | Red; latest remote run failed |
| AC-8/9/10/11 | releasable beta handoff | Red |

## Log
- spec: Added manual-first release scenario with 100% AC mapping; docgen is pending the fresh full CLI, so phase remains `spec-in-progress`.
- implement: Added a fail-closed aggregate readiness checker with positive and deliberate-red fixtures; its focused shell contract passes.
- implement: Fixed FreeBSD x86 primitive-sort architecture guards so i686 selects the scalar implementation; local cross-check now reaches the unavailable FreeBSD sysroot instead of failing on x86_64 intrinsics.
- implement: Wired SimpleOS to the produced Linux x86_64 bootstrap artifact and removed its fail-open job setting.
- implement: Made GitHub publication depend on successful bootstrap, installer, executable full-package, SimpleOS, and whole-test jobs; full-package discovery and missing-output paths now fail closed.
- implement: Updated the packaging guide to document the selected non-macOS matrix, artifact roles, and receipt gate.
- implement: Added a post-completion GitHub evidence recorder that rejects failed runs, revision mismatches, draft/missing releases, and tag mismatches; focused positive and deliberate-red contracts pass.
- implement: Enforced the selected isolated Stage 3 254-second ceiling and 24-GiB per-stage maximum-RSS ceiling in the aggregate checker, including a deliberate-red self-test.
- implement: Reworked the release matrix to seven selected non-macOS executable roles, packaged the real Linux runtime instead of its repository-only wrapper, added Linux cross-runtime producers, and made absent binaries/checksums/installers fail closed.
- implement: Added platform evidence collection from seven downloaded archives with embedded revision/version/role manifests; focused positive and revision-mismatch contracts pass.
- implement: Added exact-Stage-4 essential-tool attestation that requires all canonical test/lint/duplicate/aggregate markers, retains the log, and binds the receipt to the executable digest.
- implement: Added the canonical full FreeBSD QEMU bootstrap as a required publication dependency; cross-built FreeBSD archives no longer stand in for native bootstrap evidence. SimpleOS packaging now requires a nonempty kernel and artifact upload.
- implement: Removed per-expression/per-flat-statement bootstrap `eprint` probes from HIR lowering. They produced multi-megabyte unbuffered logs on every strict build and invalidated bounded Stage 3 timing evidence; targeted diagnostic logging remains separately gated.
- implement: Changed rebuilt seed deployment from in-place `cp` to same-directory atomic rename, so concurrent users retain the old inode instead of causing Linux `ETXTBSY`.
- verify-cycle-1: Canonical `release-beta-final` bootstrap stopped before Stage 2 when unrelated tests held the seed executable and the pre-fix installer attempted in-place overwrite (`Text file busy`).
- verify-cycle-2: After the atomic-install fix, Cargo stopped before Stage 2 because another lane changed the shared main repository to `core.bare=true` during runtime fingerprinting.
- verify-cycle-3: After restoring `core.bare=false`, the same external mutation recurred during seed fingerprinting. The main worktree invariant was restored again after the clone processes ended. Per the three-cycle cap, no fourth bootstrap was started; strict Stage 2→4 evidence remains pending.
- evidence: The fresh strict bootstrap remains owned by the already-running shared-workspace process; no competing memory-heavy build was started.
- continuation-bootstrap: With `core.bare=false` stable, one fresh cache-preserving strict retry completed Rust authority, atomic seed installation, Stage 2 native build, and Stage 2 sanity. Stage 3 was rejected after 15m13s at 9.7 GiB RSS: it remained CPU-bound in native-build, emitted no phase log or object file, and produced no candidate.
- continuation-diagnostic: A single isolated 120-second trace probe used the accepted Stage 2 compiler, one thread, a fresh cache, phase/memory tracing, and `SIMPLE_NO_STUB_FALLBACK=1`. Entry-closure discovery completed (1,758 modules), phase 2 began, the first module parsed, and the process then terminated with signal 11 while starting `src/lib/nogc_async_mut/cli/log_modes.spl` (exit 139, 173 MiB max RSS). Evidence: `build/mini_builds/release-beta-stage3-probe/probe.log`.
- blocker: AC-1 through AC-4 and all downstream fresh-CLI gates remain blocked by two reproducible Stage-3 signatures: untraced/profiler-only memory runaway before codegen and trace-enabled phase-2 SIGSEGV. No release or publication is permitted.
- diagnose: The isolated `log_modes.spl` build passes. The same full closure with streaming disabled parses beyond the second module until its bounded 30-second timeout; streaming enabled dies immediately after releasing module one. Root cause is first-time parser-global backing arrays being allocated inside the transient scope and freed while globals retain dangling handles.
- fix: Added `driver_prepare_transient_parse_scope()` to materialize reusable type/parser/AST arenas before transient tracking in both surface extraction and streaming HIR lowering. Extended the Stage-4 streaming ownership contract with before-begin ordering checks.
- verification: A canonical rebuild was started in an isolated output root, then intentionally stopped during Rust authority compilation after process audit found another active shared-tree Stage-3 build at 13+ GiB RSS. Cache is preserved; no competing strict build will be run until that owner exits.
- verify-cycle-1-after-fix: Canonical confirmation stopped before Stage 2 when concurrent Rust edits exposed a temporary five-argument caller/four-argument `lower_if` signature mismatch. The files subsequently stabilized with matching signatures; no foreign edit was changed.
- verify-cycle-2-after-fix: Rust authority compiled, but private admission failed closed because another session concurrently rebuilt `src/compiler_rust/target/bootstrap`, changing the runtime authority between its before/after snapshots. External Cargo owners remain active. Per the three-cycle cap, wait for them to exit and reserve only one final confirmation attempt.
- blocked-audit-3: The same external authority/resource condition persists for a third consecutive goal turn: an unrelated Stage-3 native build remains CPU-bound at about 6.3 GiB RSS, a shared-target Cargo build remains live, and another external bootstrap has now started. The reserved final confirmation cannot run without racing shared authority or invalidating bounded-resource evidence. Goal status may be marked blocked until those owners exit.
