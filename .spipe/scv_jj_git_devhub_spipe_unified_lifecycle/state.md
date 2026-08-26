# Feature: scv-jj-git-devhub-spipe-unified-lifecycle

## Raw Request

`$sp_dev impl scv_jj_git_devhub_spipe_unified_lifecycle_plan.md complete agent base impl`

## Task Type

feature

## Refined Goal

Implement the complete agent-owned, pure-Simple base for the unified SCV/Jujutsu/Git/DevHub/Spipe lifecycle so stable lifecycle identities, exact-revision evidence, typed protected-mutation planning, versioned provider projections, release/work objects, and policy-driven dry-run integration are persisted, queryable, fail-closed, and ready for staged authority promotion without changing current protected refs by default.

## Acceptance Criteria

- AC-1: SCV exposes persistent value-semantic identifiers and records for Change, immutable Revision, aliases, ReviewSession/Run, Finding, Approval, GateRun/Bundle, Feature, Task, ReleaseLine/Candidate/Release, RemoteBinding, SyncConflict, Publication, and operation/audit linkage; serialization round-trips every field and rejects malformed/schema-incompatible input.
- AC-2: ChangeId remains stable across revision rewrites, RevisionId changes for policy-significant tree/parent/metadata changes, and verified JJ change/commit, Git OID, and provider patchset aliases never replace the canonical SCV identity.
- AC-3: reviews, findings, approvals, and gate evidence bind to an exact immutable RevisionId plus policy/evidence digests; a changed revision marks approval stale and blocks integration until revalidation.
- AC-4: `.spipe/policy/vcs.sdn` defines protected ref classes and an observe-only parser validates schema, mutation owner, force/CAS policy, gate profile, and server-enforcement evidence; invalid, missing, contradictory, or undeclared protected operations fail closed.
- AC-5: SJ exposes typed observe, snapshot, create-change, rewrite-stack, fetch, rebase, publish-review-ref, integrate, backport, create-release-tag, publish-release-refs, recover, and break-glass operations; the compatibility surface produces the same typed plan and no new protected mutation is enabled by default.
- AC-6: typed integration planning pins base/head/expected-remote revisions, policy digest, gate profile/bundle, approvals, actor authority, lease/CAS intent, backend-equivalence checks, publication verification, and audit steps; stale remote state, stale approval, missing gate evidence, or unknown policy produces a structured refusal.
- AC-7: DevHub exposes versioned structured results for lifecycle change/review/feature/task/release/sync inspection and dry-run planning, with explicit capability discovery, idempotency identity, explain output, and unsupported-semantic errors; compatibility commands remain usable.
- AC-8: RemoteBinding synchronization computes a three-way field-authoritative plan from local, remote, and sync base values, persists conflicts instead of overwriting them, and generates replay-safe CloudEvents-compatible outbox identities.
- AC-9: `release/version.sdn` is the declared product/version compatibility source, and version render/check/explain logic detects projection drift, incompatible line/version combinations, undeclared consumers, and malformed prerelease values without editing protected publication state.
- AC-10: release state transitions distinguish candidate abandonment from immutable published release withdrawal; exact SCV revision, Git commit/tag object, source tree, gate bundle, artifacts, SBOM, provenance, and publication mappings are queryable and invalid transitions fail closed.
- AC-11: Feature, Task, Change, Revision, Run, Review, Gate, and Release remain distinct; feature manifests link layer-oriented documents and runtime `.spipe/run` state cannot silently become durable feature truth.
- AC-12: executable SSpec scenarios prove identity rewriting, approval invalidation, policy failure, integration-plan refusal, three-way sync conflict, release immutability, and malformed serialization with absolute/sabotage-sensitive oracles; every AC maps to executable evidence or an explicit active blocker.
- AC-13: the generated `doc/06_spec` manual mirrors the executable scenario, has zero stubs, uses visible steps `Load the unified lifecycle policy`, `Create stable change and immutable revision identities`, `Bind review and gate evidence to the exact revision`, `Plan a protected integration without mutating refs`, and `Project lifecycle state without silent conflict loss`, and passes all seven `sspec-maintain` dimensions without suppressed blockers.
- AC-14: pure-Simple unit/integration coverage targets at least 80% branch coverage for new code; no `pass_todo`, vacuous assertions, hard-coded success, raw runtime/env/process shortcuts, unbounded full-tree request scans, or files over 800 lines remain.
- AC-15: app-layer behavior is one-codebase across OSes; platform/provider variation is behind typed provider/HAL traits, with no per-OS DevHub/SJ application forks or duplicated adapters.
- AC-16: knowledge is refreshed in the research/design/architecture/plan and `doc/07_guide` lifecycle guide; feature- and layer-expert `skill.md` entries are created or updated; every unfixed gap is recorded under `doc/08_tracking/bug` with file:line and unblock condition; must-check v3 TODO/blocked rows name an owner and actionable unblock condition while PASS rows use `none`.
- AC-17: because this changes workflow/tooling/evidence contracts, mirrored `doc/06_spec`, `.codex/skills`, `.agents/skills`, `.claude/skills`, `.claude/agents/spipe`, `.claude/commands`, and `.gemini/commands` are updated where affected or explicitly recorded N/A with reason; generated manuals are independently reviewed as operator documentation.
- AC-18: focused Simple tests/lint/duplicate checks, generated-spec layout guard, working/staged direct-env-runtime audits, affected compiler/lib/MCP/LSP checks, and `$verify` complete once with explicit authoritative verdicts; no repeated unchanged green command is used as evidence and no more than three fix/verify cycles occur.

## Scope Exclusions

- Enabling SCV as content authority before the existing S0-S6 promotion gates pass.
- Publishing or force-updating public `main`, `release/*`, provider refs, or release tags during base implementation.
- Storing provider credentials or secrets in SCV objects, command JSON, audit events, or remote URLs.
- Claiming live remote-provider, signed-tag, or release-publication completion from mocks; unavailable external authority remains an active criterion with a Todo/resume plan.

## Cooperative Review

- Lower-model sidecars: N/A for initial shared-schema and policy ownership because concurrent edits to shared lifecycle IDs, enums, and command registry would conflict in this dirty shared worktree. Disjoint provider adapters may be delegated only after these contracts land.
- Merge owner: primary agent for common IDs, enums, provider capability schemas, CLI command registry, policy schema versions, and shared fixtures.
- Final reviewer: best available normal/highest-capability reviewer, independent of implementation authorship, for broad exclusions, generated-manual quality, and done marks.
- Shared interfaces: `LifecycleId`, `ChangeIdentity`, `RevisionIdentity`, `RevisionAliases`, `ReviewSession`, `Approval`, `GateBundle`, `RemoteBinding`, `SyncConflict`, `ProviderCapabilities`, `VcsOperation`, `IntegrateRequest`, `IntegratePlan`, `LifecycleResult`.
- Manual flow steps: `Load the unified lifecycle policy`; `Create stable change and immutable revision identities`; `Bind review and gate evidence to the exact revision`; `Plan a protected integration without mutating refs`; `Project lifecycle state without silent conflict loss`.
- Setup/checker helpers: `setup_unified_lifecycle_fixture`, `check_identity_round_trip`, `check_exact_revision_evidence`, `check_integration_plan_refusal`, `check_three_way_sync_conflict`, `check_release_transition`.
- Fail-fast placeholders: any scaffolded helper without a real oracle must call `fail("unresolved unified lifecycle oracle")`; no silent no-op or placeholder pass.
- Generated-manual review owner: final independent normal/highest-capability reviewer.

## Runtime Boundary Decision

- `runtime_need`: none; lifecycle modeling, policy parsing, dry-run planning, persistence encoding, and provider projections use existing pure-Simple facades.
- `facade_checked`: existing SCV storage, SDN, DevHub provider, SJ serialization/lease, and app I/O facades.
- `chosen_path`: `reuse-facade`, adding only the smallest owner facade if evidence proves an absent operation.
- `rejected_shortcuts`: new raw `rt_*` aliases, direct env/process externs, fixture-only mutation branches, backend field pokes, Git/JJ shell strings as canonical policy, and provider-specific app forks.

## Phase

agent-base-delivered-unverified

## Log

- dev: Created state file with 18 acceptance criteria (type: feature).
- impl: Added provider-neutral SCV lifecycle records/codec/identity/review/gate/sync/release rules, typed SJ operations/policy/integration planning, observe-only Spipe VCS policy, canonical version manifest checking, and versioned DevHub lifecycle inspection.
- impl: Added 5 focused unit/system specs (13 examples total) and a generated manual with 0 stubs. All focused examples passed diagnostically.
- verify: `bin/simple` resolved to a 60,646,096-byte Rust bootstrap seed and printed the seed warning before/after runs. Results cannot satisfy the pure-Simple production gate.
- verify: `sspec-maintain scan` and `duplicate-check` did not execute on that binary (generic CLI help, exit 1). Do not treat either as PASS.
- verify: working direct-env/runtime guard is blocked by unrelated concurrent `src/app/cli/native_build_main.spl` raw process calls; staged guard passed and this lane adds no raw runtime calls.
- verify: working numbered-artifact guard is blocked by unrelated `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`; staged guard passed and this lane adds no numbered artifact.
- impl-continuation: Added complete named base records (ReleaseLine, lifecycle Run, operation audit), digest-bound `.scv/lifecycle` record persistence, alias validation, GateBundle policy binding, conflict persistence projection, CloudEvents-compatible outbox records, work-graph identity separation, provider capability/semantic-gap records, legacy-command typed mapping, stricter protected-policy contradiction/CAS/tag checks, and DevHub inspect/version explain/render/drift helpers.
- impl-continuation: Live probes found and fixed an `inspect` dispatch shadow and unsupported prerelease `to_bytes()` call. Exact regressions now pass diagnostically.
- impl-continuation: Recorded the criterion-by-criterion base evidence and promotion boundary in `doc/03_plan/app/tools/scv_jj_git_devhub_spipe_unified_lifecycle_acceptance.md`; no diagnostic result is promoted to production evidence.
- independent-review: NOT READY. Review found unblocked gaps in typed per-entity serialization, exact approval/bundle binding, policy-derived admission, mandatory-gate parsing, projection drift checking, release identity completeness, stored inspection, CloudEvents fields, provider interfaces, executable traceability, and manual reproducibility.
- impl-continuation-2: Fixed review-head approval binding, bundle approval membership, observe-only enforcement, digest-bound policy resolution/profile matching, release-tag wildcard lookup, duplicate/malformed mandatory-gate rejection, complete immutable release publication identity, SemVer leading-zero rejection, declared projection reads, JSON escaping/stored inspection, CloudEvents envelope fields, and operator-manual command/provenance/troubleshooting accuracy. Focused changed-contract examples passed diagnostically on the seed; remaining findings stay open.
- independent-review-remediation: Added digest/schema/key-strict typed codecs for every lifecycle entity; all values traverse the canonical envelope in tests. Added canonical seven-ref policy contracts with structurally nested authoring/break-glass validation, quote/token-strict gate parsing, exact manifest-gate-to-retained-`GateRun` admission, corrupt/absent store distinction, typed conflict persistence, provider traits, and AC-tag-backed traceability.
- version-audit: Found and declared the previously omitted `src/compiler/00.common/simple.sdn` plus five product-version `.spl` projections. `version-check` discovers current product-version declarations and parses each declared `.spl` version location for drift rather than accepting a whole-file substring.
- independent-manual-review: operator-manual content is adequate for the observe-only scenario; exact command, seed/provenance warning, five frozen steps, and troubleshooting are present. Authoritative seven-dimension `sspec-maintain` remains blocked by the seed CLI.
- verification-cap: Three diagnostic verify/fix cycles were consumed. The final executed typed-codec cycle passed; subsequent source remediations received source-only independent review and scoped `git diff --check`, but were not re-executed to comply with the mandatory hard cap. They require one authoritative run in a fresh admitted-CLI session.
- delivery: The agent-owned base was committed and pushed to public `main` as `5cd33eca7717a7b87856a001fdb4f72deacfe00d`.
- delivery-waiver: The user explicitly directed publication with `--no-verify`. This closes the agent-base delivery request but creates no PASS receipt and does not promote any mutation, provider, release, or content authority.

## Implementation Handoff

The agent-owned observe-only base is implemented and its delivery request is
closed. Later authority-promotion work remains separate: live protected
integration, provider projection, policy compilation across Spipe rule
surfaces, signed tag publication, fault injection, performance evidence, and
SCV content-authority promotion.

Current-host verification prerequisite: deploy an admitted pure-Simple Stage 4
CLI at `bin/release/x86_64-unknown-linux-gnu/simple`, retain its provenance and
hash, then run exactly once:

```text
bin/simple sspec-maintain scan test/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle_spec.spl
bin/simple duplicate-check src/lib/scv/lifecycle --mode token --min-lines 5
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/numbered-artifact-guard.shs --working
```

Existing blocker record:
`doc/08_tracking/bug/deployed_bin_simple_still_seed_2026-08-05.md`.

Owner: Stage 4 bootstrap/deploy lane for the compiler prerequisite; owners of
the unrelated dirty files for their guards. Final reviewer: independent best
available normal/highest-capability maintainer.

Todo DB prerequisite: existing TODO 270 (`hardening_resume_after_seed_redeploy_2026-08-25.md`) owns the stable bootstrap-seed redeploy prerequisite; this lane does not edit the concurrently modified Todo DB.

## Process Documentation Applicability

- `doc/06_spec`: updated with the mirrored operator scenario manual.
- `.codex/skills`: N/A; the base adds no new Codex invocation contract.
- `.agents/skills`: N/A; the base adds no alternate agent skill surface.
- Spipe knowledge skills: feature- and layer-expert entries now record the
  delivered-unverified baseline, no-verify waiver semantics, and promotion
  boundary. The shared `.claude/skills/spipe.md` remains untouched because it
  is concurrently modified by another lane and its generic contract is not
  changed.
- `.claude/commands`: N/A; DevHub lifecycle is a product CLI subcommand, not a Claude command.
- `.gemini/commands`: N/A; no Gemini command consumes the observe-only base.
- Generated-manual independent review remains open until the admitted Stage 4 docgen/`sspec-maintain` pass and final independent reviewer are available.
