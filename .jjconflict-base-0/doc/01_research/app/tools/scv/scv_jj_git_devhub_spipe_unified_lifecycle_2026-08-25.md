<!-- codex-research -->
# Simple SCV + Jujutsu + Git + DevHub + Spipe

**Status:** Proposed target architecture and migration research  
**Audit date:** 2026-08-25  
**Scope:** `ormastes/simple` and `ormastes/Spipe`

## Objective

Preserve SCV's durable local evidence and Jujutsu's editing ergonomics while
retaining Git/forge interoperability. Expose one auditable lifecycle for local
and remote review, integration, releases, versions, features, tasks, and wiki
publication.

## Executive decision

Adopt a trunk-first, change-centric lifecycle with strict ownership:

| Layer | Authority |
|---|---|
| SCV | Stable lifecycle identity, immutable revisions, evidence, reviews, gates, features, tasks, releases, provenance, bindings, and operation history |
| Jujutsu | Working-copy changes, anonymous stacks, workspaces, rewriting, conflicts-as-data, and local recovery |
| Git | Forge/CI transport, interchange, signed annotated release tags, and disaster recovery |
| SJ | Sole supported mutation gateway for leases, protected refs, gates, CAS integration, publication, and audit |
| DevHub | Typed human/LLM API over SCV and remote review/task/wiki/release providers |
| Spipe | Process policy, orchestration, reviewer routing, escalation, retries, skills, and evidence collection |

Remote branches, reviews, issues, wiki pages, and releases are projections of
stable local lifecycle objects rather than local identity authorities.

## Current-state findings

1. SCV already supplies the byte-exact object/tree/commit/ref/op-log foundation;
   the missing layer is the durable software-lifecycle graph above it.
2. Migration should retain Git/JJ as content recovery authorities while SCV
   first becomes lifecycle-canonical, then later content-canonical after
   equivalence, recovery, and fault-injection gates pass.
3. Jujutsu is the correct local editor, but Git must create final signed
   annotated release tags during migration.
4. SJ currently translates command-shaped strings. It needs typed operations,
   policy evaluation, exact revisions, CAS, gate bundles, and audit records.
5. DevHub already owns useful provider/auth/facade surfaces and should be
   extended with typed domain/provider layers rather than replaced.
6. Spipe has the right orchestration shape but must become a thin client over
   DevHub and SJ, compiled from machine-readable policy.
7. Product version data is duplicated; one canonical release manifest plus
   generated projections and a fail-closed drift check is required.

## P0 safety defects

### P0-1: protected landing can bypass the complete gate set

The documented landing path reaches `jj git push`, which does not invoke Git
pre-push hooks. `sj integrate` must invoke the authoritative gate manifest
directly against pinned BASE/HEAD revisions. CI/rulesets must independently
enforce the same protected-ref contract, and a conformance test must enumerate
every protected update path.

### P0-2: direct/force updates of `main` race under parallel work

Authors use anonymous changes or isolated workspaces. `main`, `release/*`, and
release tags are protected and integration-owned. Public trunk is never
routinely force-pushed; lease-based force is limited to ephemeral review refs.

### P0-3: published tags cannot be rollback targets

Candidate refs may be abandoned before publication. Published version tags are
immutable; defective releases are withdrawn/yanked and superseded by a new
patch release.

### P0-4: approvals are not exact-revision evidence

Every approval must bind review ID, immutable RevisionId, patch/tree digest,
reviewer authority, policy/evidence digests, time, and optional signature. Any
source change invalidates approval until revalidation.

### P0-5: version and provenance are not unified

Structured version output and release artifacts must identify product version,
channel, SCV revision/change-set, Git commit, tree/build/artifact digests,
compiler lineage, backend set, reproducible epoch, and attestation ID.

## Resulting design rules

- Use `main`, supported `release/X.Y` lines, immutable `vX.Y.Z[-pre]` tags,
  anonymous JJ changes, and provider-required ephemeral review refs.
- Represent local reviewed trunk as protected `integration/main`, shown as
  `main@local`, separate from `main@origin` and public `main`.
- A release branch represents a supported compatibility line, never a version.
- Product SemVer, release channel, store/wire/provider/skill/package schemas,
  compiler ABI, and bootstrap protocol remain separate version axes.
- Reviews start with intent/design/risk and bind all findings and approvals to
  immutable revisions with parser-aware anchors.
- Model review is a bounded evidence-driven DAG: deterministic checks, fast
  reviewer, strong reviewer, independent specialist, then human authority.
  Default depth is three model tiers, fan-out two, with cycle detection.
- Use SARIF 2.1 for finding interchange, an OSLC-CM-inspired lifecycle
  vocabulary, and CloudEvents-compatible outbox envelopes.
- Synchronization is three-way and field-authoritative. No timestamp-only
  last-write-wins and no silent provider-semantic flattening.
- Feature, Task, Change, Revision, Review, Gate, Release, and Run remain
  distinct objects. Runtime run state is never durable feature truth.

## Canonical lifecycle relationships

```text
Feature implements Requirements
Task contributes_to Feature
Change implements Task or Feature
Revision snapshots Change immutably
Review evaluates Revision
Gate verifies Revision
Release contains Revision
RemoteBinding projects lifecycle objects
```

## Required policy sources

Create `.spipe/policy/{vcs,review,release,version,task_feature,
provider_sync,model_route,authority}.sdn`. A policy compiler must generate agent
rules, skill contracts, guide tables, and gate-manifest entries, and fail on
missing enforcement, contradictory authority, drifted projections, or protected
mutations without server-side evidence.

## Migration ordering

1. Correct protected-ref and landing safety.
2. Add SCV lifecycle identities in shadow mode.
3. Add local review and protected local integration.
4. Add canonical versions and release lifecycle.
5. Project reviews/releases to GitHub.
6. Add feature/task/wiki binding and synchronization.
7. Add providers through a common capability contract.
8. Promote SCV content authority only after existing S0-S6 migration gates.

## Research basis

Repository evidence includes the existing SCV research/architecture/design,
migration plans, SJ translator and service design, DevHub adapters/facades,
Spipe release/review skills, VCS rules, landing wrapper, release workflow,
`VERSION`, and compiler provenance checks.

External foundations reviewed include official Jujutsu, SemVer, DORA, GitHub,
GitLab, Gerrit, Review Board, SARIF, OSLC-CM, CloudEvents, and ForgeFed guidance;
branching-quality studies by Shihab et al. and Phillips et al.; modern review
research by Sadowski et al. and McIntosh et al.; and selective model-cascade and
calibrated-deferral literature. The routing policy requires project-specific
calibration rather than trusting raw model confidence.

## Decision log

| Concern | Decision |
|---|---|
| Local isolation | Anonymous JJ changes/workspaces |
| Public topology | Trunk plus supported `release/X.Y` |
| Change identity | SCV-native stable ID with aliases |
| Review identity | Exact immutable SCV RevisionId |
| Release identity | Signed annotated Git tag via SJ during migration |
| Provider API | Extend DevHub with typed capabilities |
| Feature/task truth | SCV/local manifest with provider bindings |
| Sync | Three-way, field-authoritative |
| Reviewer escalation | Bounded evidence-driven DAG |
| Gate enforcement | Typed SJ transaction plus independent CI |
| Skill source | Machine-readable Spipe policies |

