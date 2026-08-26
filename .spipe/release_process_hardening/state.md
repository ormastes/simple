# Feature: release_process_hardening

## Raw Request

> $sp_dev with the research doc improve versioning, release skill/process. updated spipe skill doc and others. adn improve spipe plugin. and check it works well for release beta. and beta process should cherrypick other bug fixes. plan design and imple and check with simple release. make a general rules and guiede and skill of sw release.

Research input:
`doc/01_research/infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md`

## Task Type

feature

## Refined Goal

Implement and verify one policy-driven Simple/Spipe software-release system in which canonical versions, isolated release sessions, beta maintenance and reviewed bug-fix cherry-picks, immutable candidates, signed promotion without rebuild, generated release skills/plugin commands, and operator guidance all agree and fail closed.

## Acceptance Criteria

- AC-1: A selected feature-requirements document and NFR document define the stable, alpha/beta/RC, maintenance-line, cherry-pick/backport, candidate, promotion, withdrawal, and compatibility rules; no `*_options.md` remains after selection.
- AC-2: `release/version.sdn` is the canonical Simple product-version authority, and one focused checker proves all declared projections agree, rejects a deliberately stale projection, validates lowercase numbered SemVer prereleases such as `X.Y.Z-beta.N`, and rejects legacy/new malformed release identities.
- AC-3: The typed VCS/release policy defines protected `main`, `release/*`, `candidate/*`, and `v*` refs, one session branch plus one worktree per mutation lane, allowed rebase/ref mutation by class, exact single-tag push, signed annotated immutable tags, and fail-closed live-policy drift checks.
- AC-4: The beta process creates or uses `release/X.Y`, prepares `X.Y.Z-beta.N` from an exact protected revision, and accepts bug fixes only through a reviewed cherry-pick/backport command that records source commit, stable change/work ID, target line, adaptation reason, and renewed focused evidence; unrelated features and direct protected-ref edits are rejected.
- AC-5: A release candidate is create-once and binds version, exact commit, policy/version/toolchain/source digests, required support rows, and evidence identities; promotion consumes that admitted candidate and its exact artifacts without rebuilding or selecting moving/fallback binaries.
- AC-6: Release rollback/withdrawal never moves, deletes, or reuses a published version/tag; operational rollback redeploys an earlier admitted release and source correction creates a new beta/RC/patch identity.
- AC-7: Simple exposes focused release commands sufficient to render/check/bump versions, prepare beta release metadata, verify a backport, create/inspect a candidate, and dry-run promotion; commands reject main-worktree mutation, stale expected SHAs/policy hashes, missing admission evidence, unsigned/lightweight tag plans, all-tag pushes, and rebuild-on-promote plans.
- AC-8: The Spipe plugin manifest declares the new release/session/candidate policy schema and capabilities with an appropriate pre-1.0 compatibility bump; Spipe CLI/MCP/skill projections expose guarded release and beta-backport operations and no generic protected-ref mutation or tag-delete capability.
- AC-9: The canonical Spipe release semantic source and all affected `.codex/skills/`, `.agents/skills/`, `.claude/skills/`, `.claude/agents/spipe/`, `.claude/commands/`, and `.gemini/commands/` projections agree on canonical version input, isolated sessions, beta cherry-pick policy, immutable candidates, signed exact tag promotion, no rebuild, and no destructive tag rollback; a parity gate rejects reintroduced legacy behavior.
- AC-10: A general software-release architecture, detailed design, system-test plan, agent-task plan, operator guide, and reusable release skill explain the complete stable/prerelease workflow, authority boundaries, beta cherry-pick rules, failure recovery, exact commands, receipts, and unsupported/blocked states without advertising behavior unreachable through the shipped Simple/Spipe binaries.
- AC-11: Executable SSpec scenarios with REQ-to-test traceability cover beta preparation, allowed and rejected bug-fix cherry-picks, canonical-version drift, candidate immutability, promote-not-rebuild, exact signed-tag planning, withdrawal, plugin projection parity, and at least one adjacent adversarial case for each trust boundary; the mirrored `doc/06_spec` Markdown reads as a standalone operator manual and no executable `.spl` exists beneath `doc/06_spec`.
- AC-12: The implementation uses pure-Simple owner modules and existing VCS/process facades; any unavoidable runtime/process boundary is documented with `runtime_need`, `facade_checked`, `chosen_path`, and `rejected_shortcuts`, and both working/staged direct-env-runtime guards remain clean for owned changes.
- AC-13: Focused verification runs each acceptance gate once, includes Simple release beta dry-run and rejection fixtures, plugin build/parity checks, lint and token duplicate-check for changed `.spl`, exact candidate identity checks, and the release-bound whole test command `bin/simple test test --whole --mode=interpreter`; required failures/fallbacks cannot yield PASS and the lane stops after at most three distinct fix/verify cycles.
- AC-14: Knowledge is updated in the saved research doc, feature/NFR requirements, architecture, design, plans, generated/manual spec, `doc/07_guide`, and both feature- and layer-expert `skill.md` pages; remaining gaps receive `doc/08_tracking/bug/` records with file:line and unblock conditions, and any must-check ledger v3 TODO/blocked row has an owner and actionable unblock condition while PASS uses `none`.
- AC-15: The final audit maps every AC to current authoritative file or command evidence, distinguishes current-host/implementation handoff from full completion, and does not mark verify/release/goal complete while any required host, policy, signing, whole-suite, generated-manual, or plugin-projection evidence is missing.
- AC-16: An active beta/bootstrap lane performs bounded read-only discovery of reviewed fixes diverging between exact `main` and `release/X.Y` snapshots; each selected fix crosses through an isolated reviewed backport or forward-port and protected CAS integration, emits a divergence receipt, and never makes `main` track or become the release branch.

## Scope Exclusions

- Pushing protected refs, publishing a GitHub release, publishing registry packages, changing live GitHub rulesets, or using real signing keys without separate explicit authorization.
- Rewriting the existing bootstrap stage engine or implementing the complete speculative bootstrap DAG; this lane may define its release-facing admission contract and preserve it in architecture/design for a separate implementation lane.
- Deleting or renaming legacy published tags.
- Automatically selecting or cherry-picking arbitrary bug fixes: only caller-identified, reviewed commits with exact provenance are admissible.

## Cooperative Review

- Lower-model sidecars: local inventory of version/release implementation; Spipe skill/plugin projection inventory; beta/backport and adversarial-test inventory; documentation/expert-page inventory.
- Merge owner: primary Codex `/root` agent.
- Final reviewer: primary normal/highest-capability Codex agent after sidecar findings are reconciled.
- Shared interfaces: `ReleaseVersion`, `ReleaseChannel`, `ReleasePolicy`, `ReleaseSession`, `BackportRequest`, `CandidateManifest`, `ReleaseAdmission`, `PromotionPlan`, `ReleaseReceipt`.
- Manual flow helpers: `step("Load the canonical release policy")`, `step("Prepare an isolated beta release")`, `step("Admit reviewed bug-fix backports")`, `step("Reconcile reviewed fixes with main")`, `step("Freeze and qualify the release candidate")`, `step("Promote exact admitted artifacts")`, `step("Withdraw without rewriting release identity")`.
- Setup/checker helpers: `setup_release_fixture`, `check_version_projection`, `check_backport_admission`, `check_candidate_manifest`, `check_promotion_plan`, `check_release_projection_parity`.
- Fail-fast placeholders: unresolved scaffolds use `assert(false)` or `fail(...)`; no placeholder PASS is admissible.
- Generated-manual review owner: primary Codex agent; sidecars may inventory but may not accept manual quality or done marks.

## Phase

verify-blocked

## Log

- dev: Created state file with 15 acceptance criteria (type: feature).
- research/design: Saved the audit, selected requirements/NFRs, architecture,
  detailed design, system-test plan, and parallel-agent ownership plan.
- implementation: Added typed release policy/CLI checks, beta backport admission,
  immutable candidate/promotion checks, normalized `1.0.0-rc.1` projections,
  software-release guides/skills, and Spipe 0.2.0 release capabilities.
- isolation: Fetched GitHub before creating
  `work/release/local-20260826-001-release-process-hardening` in
  `/mnt/data/worktrees/simple-release-process-hardening`; rebased the private
  branch onto current `origin/main` after implementation.
- focused verification: release SSpec 6/6 PASS; version-manifest spec 5/5 PASS;
  Spipe build/parity PASS; direct-env runtime guards working/staged PASS.
- review: lower-model inventory lanes and implementation/docs plugin reviews
  completed; highest-capability release review requested after reconciliation.
- convergence policy: Added bounded read-only main/release discovery, exact reviewed
  backport and forward-port paths, protected CAS integration, divergence receipts,
  and the invariant that `main` remains trunk rather than tracking a release line.
- highest review: Top-level direct-main rules were corrected. Final review still
  rejects completion because convergence is not Git/CI-wired, candidate/admission
  schemas diverge, promotion retries and remote asset checks are incomplete, npm
  packages are rebuilt after admission, projection parity is partial, and version
  discovery misses JSON consumers and exceeds its latency target.
- blocked: release-grade whole-suite/lint evidence cannot be claimed with the
  available runtime because it identifies itself as bootstrap seed-derived.
  Live GitHub ruleset verification and promote-only workflow conversion remain
  outside the authorized live-mutation scope and are tracked separately.
