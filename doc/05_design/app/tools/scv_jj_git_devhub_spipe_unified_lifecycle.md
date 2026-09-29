<!-- codex-design -->
# Unified SCV/JJ/Git/DevHub/Spipe lifecycle design

**Status:** Design for staged implementation  
**Research (authority):**
`doc/01_research/app/tools/scv/scv_jj_git_devhub_spipe_unified_lifecycle_full_2026-08-25.md`
(doc 1) and
`doc/01_research/app/tools/scv/scv_jj_git_unified_release_review_work_item_2026-08-25.md`
(doc 2)  
**Architecture:** `doc/04_architecture/app/tools/scv_jj_git_devhub_spipe_unified_lifecycle.md`  
**Measured state:** file:line citations below are against the tree on 2026-09-05;
anything labelled *src-lane delta* is NOT implemented.

## Design goals

- Make lifecycle identity and evidence durable and locally usable.
- Preserve JJ editing and Git/forge compatibility during migration.
- Permit exactly one policy-checked mutation path for protected state.
- Make local review, remote review, integration, and product release distinct.
- Introduce functionality incrementally without rewriting existing SCV,
  DevHub, SJ, or Spipe surfaces.

## Ownership and dependency direction

```text
Human / LLM / IDE
        |
      Spipe                 policy/orchestration only
        |
      DevHub                typed lifecycle/provider API
      /    \
    SCV     SJ              durable graph / serialized mutations
             \
             JJ + Git       editing backend / public transport
```

SCV lifecycle modules must not depend on provider implementations. DevHub
domain objects depend on lifecycle interfaces; provider adapters implement
capability traits. SJ consumes typed requests and policy decisions but does not
own review/task/wiki business logic. Spipe consumes versioned JSON results.

## Core identifiers and records

Introduce opaque IDs for Change, Revision, Review, ReviewRun, Finding,
Approval, GateRun, GateBundle, Feature, Task, ReleaseLine, ReleaseCandidate,
Release, RemoteBinding, SyncConflict, and Publication.

`ChangeId` remains stable across rewrites. `RevisionId` is derived from the
immutable tree, parents, and policy-required metadata. JJ change/commit IDs,
Git OIDs, and provider patchsets are verified aliases, never canonical IDs.

Approvals and findings contain the exact RevisionId and evidence/policy
digests. Findings use semantic anchors (path, parser, symbol, syntax-node and
token fingerprints, entity ID) with line/column only as fallback.

## SCV lifecycle capsules

Module layout is **fixed** (decision, supersedes the earlier "suggested"
list). It follows doc 1 §11.2's shape rooted at the paths that already exist;
doc 2 §15's `src/lib/scv/*.spl` flat set and `src/lib/dev/` / `src/app/dev/`
roots are **not adopted** — DevHub is the `dev` tool (doc 1 §1.5: extend, do
not replace) and the lifecycle capsule already lives under `src/lib/scv/lifecycle/`.

```text
src/lib/scv/lifecycle/                 value objects only; no JJ/Git/provider imports
  model.spl          all lifecycle structs + LifecycleResult        (exists, 224 lines)
  identity.spl       ChangeId/RevisionId derivation, alias checks   (exists)
  codec.spl, entity_codec.spl   scv-lifecycle/1 field vectors       (exists)
  store.spl          .scv/lifecycle/<kind>/<id>.scvl facade         (exists)
  review.spl         open/approve/revalidate, gate bundle admission (exists)
  routing.spl        escalation policy + admission                  (exists)
  release.spl        candidate/release transitions                  (exists; gaps below)
  work.spl           feature/task/run validation                    (exists)
  sync.spl           field plan, conflict persist, outbox event     (exists)
  audit.spl          operation audit records                        (exists)
  -- Stage 3 additions go INTO model.spl/release.spl (ReleasePlan,
     VersionDecision, BackportRecord); no new file until a second consumer exists.

src/app/sj/                            typed mutation vocabulary + pure planning
  operation.spl, integrate_plan.spl, gate_manifest.spl, lifecycle_policy.spl (exist)

src/app/devhub/
  cmd_lifecycle.spl                    versioned inspection surface (exists)
  version_manifest.spl                 release/version.sdn parse/render/drift (exists)
  provider/lifecycle_capability.spl    capability records (exists; must change, see below)
  provider/lifecycle_provider.spl      5 traits, 0 implementers (exists)
  provider/registry.spl                provider_id -> adapter lookup (Stage 4 src-lane delta)
  provider/<github|gitlab|gerrit|reviewboard|bitbucket>/   Stage 4/6a typed adapters
      capabilities.spl  review.spl  task.spl  knowledge.spl  release.spl
  adapter_*.spl                        existing transports; typed adapters call them,
                                       Spipe and domain code never do

test/01_unit/lib/scv/lifecycle_*_spec.spl        capsule specs (6 exist)
test/01_unit/app/sj/*_spec.spl                   planner specs (6 exist)
test/01_unit/app/devhub/lifecycle_*_spec.spl     command + capability specs (2 exist)
test/01_unit/app/devhub/provider_contract/<name>_spec.spl   Stage 6a contract suite
```

Policy and manifest roots: `.spipe/policy/vcs.sdn` (protected refs, schema
`spipe-vcs/3`) and `release/version.sdn` (schema `simple-release-version/1`).

Each capsule exposes value-semantic records and a narrow store trait. Object
encoding and migration remain behind `store.spl`; provider formats do not enter
these modules. Cross-cutting audit/provenance is emitted as lifecycle operation
records rather than hidden callbacks.

The base codec uses schema `scv-lifecycle/1`, a canonical ordered field vector,
field count, and SHA-256 digest. Records live under
`.scv/lifecycle/<kind>/<entity-id>.scvl`; unsafe path/delimiter input and digest
or field-count mismatch fail before admission.

## Typed SJ transaction boundary

Replace mutation string translation progressively with a `VcsOperation` sum:
observe, snapshot, create change, rewrite stack, fetch, rebase, publish review
ref, integrate, backport, create release tag, publish release refs, recover, and
raw break-glass. Compatibility parsing may construct this AST.

Measured: `src/app/sj/operation.spl:18-23` is a `struct VcsOperation: kind:
text` plus 13 string constants (`:4-16`) validated by `vcs_operation_valid`
(`:28`), not a sum type. Decision: keep the string-kind struct through Stage 2
— it is the wire form Spipe sees in JSON and the planner only needs `kind` +
`entity_id` + `target_ref`. Per-kind request payloads (doc 1 §15.1) are
introduced as **separate structs carried alongside** (`IntegrateRequest`
already exists at `integrate_plan.spl:8-19`; `CreateReleaseTagRequest` and
`BackportRequest` are Stage 3 src-lane deltas). Converting to an `enum` with
payloads is allowed once every kind has a request struct; it is not a
prerequisite for any stage exit.

Ref classes are policy rows: `ProtectedRefPolicy`
(`src/app/sj/lifecycle_policy.spl:6-12`) resolved by `lifecycle_policy_ref`
(`:311`). `.spipe/policy/vcs.sdn:5-52` carries seven of the eight doc 1 §7.1
classes; the private/security namespace row is a Stage 0 policy delta.

`IntegrateRequest` contains exact candidate/base/expected-remote revisions,
target ref, policy digest, required gate profile, approvals, actor authority,
and dry-run/explain flags.

Integration state machine:

```text
resolve -> lease -> fetch/CAS-check -> refresh candidate
        -> invalidate stale review -> execute pinned gates
        -> verify SCV/JJ/Git trees -> CAS integration/main
        -> export/publish -> verify remote -> audit complete
```

Any mismatch aborts before publication. Gate correctness does not depend on
hooks. CI/rulesets independently repeat protected checks.

The planner emits exactly these nine steps today (`integrate_plan.spl:54-64`)
and rejects non-dry-run with `SJ_OBSERVE_ONLY` (`:33-34`). The executor that
walks the steps is the Stage 2 src-lane delta. Interaction, once executed:

<!-- sdn-diagram:id=scv_jj_git_devhub_spipe_unified_lifecycle.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_jj_git_devhub_spipe_unified_lifecycle.design hash=sha256:auto render=ascii
@layout dag
@direction LR

Spipe -> DevHub_integrate
DevHub_integrate -> SJ_plan_integration
SJ_plan_integration -> SCV_gate_bundle_admits
SJ_plan_integration -> SCV_approval_revalidate
SJ_plan_integration -> SJ_lease
SJ_lease -> Git_fetch_cas_compare
Git_fetch_cas_compare -> JJ_refresh_candidate
JJ_refresh_candidate -> SCV_revision_identity
SCV_revision_identity -> GateEngine_pinned_manifest
GateEngine_pinned_manifest -> SCV_tree_equivalence
SCV_tree_equivalence -> Git_cas_integration_main
Git_cas_integration_main -> Git_push_exact_refspec
Git_push_exact_refspec -> Git_verify_remote
Git_verify_remote -> SCV_operation_audit
SCV_operation_audit -> SJ_release_lease
SJ_release_lease ~> DevHub_integrate
DevHub_integrate ~> Spipe
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_jj_git_devhub_spipe_unified_lifecycle.design hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

A changed `RevisionId` at `SCV_revision_identity` routes back to review
(`revalidation_required`), never forward; a changed remote head at either CAS
step is a retry/rebase/re-review, never a force push (doc 1 §15.4).

## DevHub typed domain/provider layer

Add domain commands for change, review, integrate, feature, task, release, and
sync while retaining compatibility commands. Providers advertise nested source,
review, task, knowledge, release, identity, and automation capabilities.

Every command supports versioned JSON, idempotency keys, dry-run, and explain.
Unsupported semantics fail explicitly. A local blocking verdict must not be
silently projected as a non-blocking provider comment.

`RemoteBinding` stores local entity identity, provider instance/kind/ID,
remote revision or ETag, authority policy, last pull/push digests, sync base,
and state. Synchronization computes a field-level three-way plan and persists
conflicts. Webhooks use a durable idempotent CloudEvents-compatible outbox.

Measured: `RemoteBinding` (`src/lib/scv/lifecycle/model.spl:102-112`) carries
`remote_revision` and `sync_base_digest` but not doc 1 §12.1's
`last_pulled_digest` / `last_pushed_digest` / `remote_head_alias`. Decision:
`sync_base_digest` + `remote_revision` are sufficient for the three-way plan
(`sync.spl:30` compares base/local/remote values, not pull/push history);
pull/push digests are recovered from `OperationAudit` records
(`audit.spl:18`) rather than duplicated on the binding. `remote_head_alias` is
added only when a review binding exists (Stage 4, on `ReviewSession` bindings
per doc 1 §10.1 "comments cannot be posted against a different revision").

### Capability records (must change — Stage 4/6a src-lane delta)

`ProviderCapabilities` (`src/app/devhub/provider/lifecycle_capability.spl:16-24`)
nests `review: ReviewCapabilities?` but flattens `task`, `knowledge`,
`release`, `automation` to `bool`. A bool cannot express a Jira workflow or a
Confluence page hierarchy, which Stage 6a's "no false equivalence" rule (doc 1
§17.2) requires. Target shape (doc 1 §11.3):

```text
struct ProviderCapabilities:
    provider_id: text
    api_version: text
    source: bool
    review: ReviewCapabilities?
    task: TaskCapabilities?          # was bool
    knowledge: KnowledgeCapabilities?  # was bool
    release: ReleaseCapabilities?    # was bool
    automation: bool                 # stays bool until an automation op exists

struct ReviewCapabilities:           # exists at :6-14; add the last four
    create_review, pre_commit_review, inline_threads, approve,
    request_changes, patchsets, dependent_changes, merge_queue: bool
    batch_review: bool
    native_stacks: bool
    suggested_patches: bool
    verdict_model: text              # "approve_request_changes" | "labels" | "ship_it"

struct TaskCapabilities:
    create, query, transition, link, append_comment: bool
    workflow_model: text             # "open_closed" | "arbitrary_workflow"

struct KnowledgeCapabilities:
    publish, fetch, diff, attach, search: bool
    page_model: text                 # "flat" | "hierarchy" | "repo_page"

struct ReleaseCapabilities:
    create_draft, upload_asset, publish, withdraw, query_attestations: bool
```

One discriminator field per domain (`verdict_model`, `workflow_model`,
`page_model`) is the whole "preserve, do not flatten" mechanism; it is not a
schema. `provider_review_operation` (`:26`) keeps its strict-sync refusal.

### Provider trait adequacy (measured 2026-09-05)

`src/app/devhub/provider/lifecycle_provider.spl:9-31` declares
`LifecycleProvider`, `ReviewProvider`, `TaskProvider`, `KnowledgeProvider`,
`ReleaseProvider`, all returning `LifecycleResult`, all writes carrying an
`idempotency_key`, all reads carrying `expected_revision`. **Zero
implementers exist.** Verdict: the shape is adequate (trait-per-capability,
CAS reads, idempotent writes match doc 1 §11.4/§12.2); the operation sets are
not. Required changes, driven by the Stage 6a providers rather than by doc 1
§11.4's full list:

| Trait | Keep (`:13-31`) | Add | Why |
|---|---|---|---|
| `ReviewProvider` | `fetch_review`, `publish_revision`, `publish_findings`, `submit_verdict` | `create_review(change_id, revision_id, key)`, `fetch_threads(review_id, revision_id)`, `resolve_thread(review_id, thread_id, key)`, `enqueue_or_merge(review_id, revision_id, key)`, `close(review_id, reason, key)` | Review Board pre-commit review has no pushed branch to `fetch`; Gerrit creates the change server-side; thread resolution is the anchor round-trip |
| `TaskProvider` | `fetch_task`, `apply_task_plan` | `create_task(feature_id, task_id, key)`, `query(filter)` | **Decision:** the sync plan is the only write — no `update_fields`/`transition` entry points. This narrows doc 1 §11.4 deliberately so no unplanned field write can bypass field authority |
| `KnowledgeProvider` | `fetch_document`, `apply_managed_regions` | `publish_document(document_id, key)`, `diff(document_id, expected_revision)` | first publish of a page; managed-region apply stays the only update path |
| `ReleaseProvider` | `create_draft`, `upload_asset`, `verify_publication`, `withdraw` | `publish(release_id, expected_revision, key)`, `query_attestations(release_id)` | draft -> locked is a distinct remote transition (doc 1 §9.5 step 9) |
| `SourceProvider`, `IdentityProvider`, `AutomationProvider` | — | deferred | no stage before 7 needs them; do not declare unused traits |

Traits stay traits: adapters are structs that implement them (composition,
no inheritance). A provider that lacks a capability implements the trait
method by returning `lifecycle_error("PROVIDER_UNSUPPORTED", ...)` — never a
silent no-op success.

## Review engine

Review lifecycle:

```text
draft -> evidence_collecting -> reviewing
      -> changes_requested | approved | abstained
      -> revision_updated -> revalidation_required -> approved -> integrated
```

Profiles are quick, standard, architecture, security, concurrency, performance,
release, and mission-critical. Routing combines deterministic evidence, risk
ownership tags, reviewer disagreement, missing evidence, analysis coverage, and
calibrated historical outcomes. It does not approve from self-confidence alone.

Default escalation constraints: depth 3, children 2, normalized-question cycle
detection, no same-reviewer repeated question, explicit missing-evidence
statement, and human disposition for unresolved high/critical findings.

## Version and release design

Use `release/version.sdn` as the product/version and compatibility-axis source.
Declared projections replace hard-coded release edits. `devhub version render`,
`check`, and `explain` manage and validate mirrors.

Release state:

```text
planned -> candidate_created -> source_frozen -> verified -> reviewed
        -> tagged_staging -> artifacts_staged -> publication_ready
        -> published -> verified_remote -> closed
```

Before publication a candidate can be abandoned. After publication it can only
be withdrawn and superseded. SJ creates the signed annotated Git tag, records
the tag object/signature/commit/SCV revision mapping, publishes with CAS, and
DevHub verifies remote artifacts and attestations.

### State vocabulary (decision)

The doc 1 §9.1 vocabulary above is canonical. Doc 2 §7.1's vocabulary folds
in as follows, not as a second machine: `supported` / `end_of_support` are
`ReleaseLine.support_state` values (`planned -> maintained -> security_only ->
end_of_life`, doc 1 §7.5, `model.spl:186`); `revoked` and `yanked` are
`withdrawn` with a reason category on the withdraw operation; `superseded` is
a `supersedes` relation from the replacement release (doc 1 §17.1), not a
state; `verified_candidate`/`approved` are `verified`/`reviewed`.

Measured gap (Stage 3 src-lane delta): `release.spl:6-15` admits
`reviewed -> publication_ready` directly — `tagged_staging` and
`artifacts_staged` are missing from the candidate machine — and `:17-27`
knows only `publication_ready -> published -> withdrawn`, so `verified_remote`
and `closed` are absent. `ReleaseIdentity` (`model.spl:190-204`) lacks
`tag_signature` (doc 1 §5.6); the publish precondition at `release.spl:22-23`
must additionally require it once SJ produces signed tags.

### Release plan and version decision

Add to `model.spl` (Stage 3 src-lane delta; shapes from doc 2 §7.3, §7.6,
doc 1 §7.4):

```text
struct ReleasePlan:
    plan_id: text
    line_id: text
    base_release_id: text
    target_revision_id: text
    included_change_ids: [text]
    excluded_change_ids: [text]
    candidate_version: text
    decision: VersionDecision
    gate_profile: text
    unresolved_questions: [text]

struct VersionDecision:
    recommended: text          # major | minor | patch | none | prerelease
    confidence_evidence: text  # digest of the inputs that ran
    reasons: [text]
    breaking_entities: [text]
    analysis_ran: bool         # false => FAIL for channel=stable
    override_required: bool

struct BackportRecord:
    source_change_id: text
    source_revision_id: text
    target_line_id: text
    resulting_change_id: text
    resulting_revision_id: text
    conflict_resolution_digest: text
    equivalence_review_id: text
    state: text                # planned | integrated | waived
```

`lifecycle_release_plan_admits(plan) -> LifecycleResult` is fail-closed:
`analysis_ran == false` on a stable channel is `FAIL`
(`LIFECYCLE_VERSION_UNANALYZED`), an empty `included_change_ids` is `ERROR`
(nothing was planned), `override_required` without an approval id is `FAIL`.
Inputs to the decision are the doc 2 §7.6 list (public API diff, ABI diff,
grammar diff, storage/protocol format diff, dependency graph, behaviour
contracts, deprecation policy, declared work-item impact, human override);
the minimum-bump table is doc 1 §8.3.

Version manifest: `release/version.sdn` is the single source
(`simple-release-version/1`, product/semver/line/channel, 10 compatibility
axes, declared projections). `src/app/devhub/version_manifest.spl` already
provides `parse_version_manifest` (`:114`), `render_version_manifest`
(`:193`), `version_projection_drift` (`:213`), `version_undeclared_consumers`
(`:225`) and `version_explain` (`:238`). `devhub version check` FAILs on any
drift or undeclared consumer and ERRORs when the manifest is unparseable —
it never reports clean on an empty projection list. Legacy `1.0.0-RC` is
accepted as input; new candidates normalize to `-rc.N` (doc 1 §8.4).

### Tag rules (SJ, doc 2 §7.5)

`sj create_release_tag` fails if the name exists; there is no force update in
`refs/tags/v*` (`vcs.sdn:27-32`, `immutable_annotated_signed`); candidates are
`candidate/<version>/<id>` refs (`vcs.sdn:41-46`, `create_once`), never tags;
tag, annotation, release object, source commit/tree and signature are verified
together; Git export must resolve the tag to the mapped commit before
`publish_release_refs`. Revoke is metadata only.

### Emergency fixes and backports

Default path is fix on `main`, then one `BackportRecord` per maintained line
with the release-line gate profile (doc 1 §7.3). A release-line-first fix is
admitted only with a forward-port `Task` created in the same operation; the
release cannot reach `publication_ready` while that task is open and unwaived.

## Feature/task/document projection

Durable feature manifests live under
`doc/08_tracking/feature/<FeatureId>/feature.sdn` and link substantive research,
plan, architecture, design, and spec documents in their existing layer trees.
Runtime state remains under `.spipe/run/<run-id>/state.sdn`.

Wiki synchronization uses managed regions plus a sync base so remote-maintained
content is preserved. Task and feature mutations always target an explicit
binding or displayed sync plan.

## Stage 6a — provider expansion

The plan's "Stage 6" covers both provider expansion (6a, here) and policy
compilation (6b, next section). Order: GitLab, Gerrit, Review Board, Bitbucket
typed completion (doc 1 §19 Phase 6). GitHub is the Stage 4 baseline every
new provider is measured against, not a template it must copy.

### Per-provider capability records

Values below are the **declared** records each adapter's `capabilities.spl`
returns from `discover_capabilities`; a provider fixture asserts them, and the
fixture — not this table — is the authority once it exists (forge features
vary by version and instance; doc 1 §11.5 names the class of gap, not the
forge's current API). `-` means the trait method returns
`PROVIDER_UNSUPPORTED`.

| Capability | GitHub | GitLab | Gerrit | Review Board | Bitbucket |
|---|---|---|---|---|---|
| `review.create_review` | yes (PR) | yes (MR) | yes (change, server-side) | yes (review request) | yes (PR) |
| `review.pre_commit_review` | - | - | yes (patchset) | **yes, no pushed branch** | - |
| `review.inline_threads` | yes | yes (discussions) | yes | yes | yes |
| `review.batch_review` | yes (grouped review) | yes | yes (draft comments) | yes | - |
| `review.approve` | yes | yes (approvals) | via label | ship-it | yes |
| `review.request_changes` | yes | - (no native state) | via label | - | - (needs-work flag only) |
| `review.patchsets` | commits | versions | **yes, first-class** | diff revisions | commits |
| `review.dependent_changes` | - | - | yes (topics/relation chain) | depends-on | - |
| `review.native_stacks` | stacked PRs where enabled | stacks | yes | - | - |
| `review.merge_queue` | yes where enabled | merge trains | submit queue | - | - |
| `review.suggested_patches` | yes | yes | - | - | - |
| `review.verdict_model` | `approve_request_changes` | `approve_request_changes` | `labels` | `ship_it` | `approve_request_changes` |
| `task.*` | issues | issues | - | - | issues (limited) |
| `task.workflow_model` | `open_closed` | `open_closed` | - | - | `open_closed` |
| `knowledge.*` | wiki (repo pages) | wiki (repo pages) | - | - | wiki |
| `knowledge.page_model` | `repo_page` | `repo_page` | - | - | `repo_page` |
| `release.*` | releases + assets | releases + assets | - | - | downloads only |

Jira (`arbitrary_workflow`) and Confluence (`hierarchy`) remain task/knowledge
providers on the existing `adapter_jira*.spl` / `adapter_confluence.spl`
transports and are typed in this stage only if a contract fixture exists.

### What each provider must NOT flatten (doc 1 §11.5, §17.2)

| Provider | Preserved semantics | Forbidden projection |
|---|---|---|
| GitHub | grouped PR reviews, requested reviewers, queue | posting per-finding comments as one summary comment |
| GitLab | MR discussions, approval rules, merge trains | mapping a local `request_changes` verdict to a plain note — wherever the declared record has `request_changes: false`, strict sync **refuses**, lenient sync posts an explicitly non-equivalent note and keeps the block local |
| Gerrit | stable Change-Id (an alias of `ChangeId`), patchsets, label vocabulary, topics, dependent submission | reducing labels to approve/request-changes when `verdict_model` is `labels`; the label-to-verdict mapping is declared per instance, never assumed |
| Review Board | pre-commit review from a local diff | manufacturing a fake `review/*` ref to satisfy `fetch_review` |
| Bitbucket | comments, approvals, merge strategies | reporting `request_changes` support the declared record does not claim; a partial native equivalent is projected as `PROVIDER_PARTIAL` with the gap named in the result |
| Jira | arbitrary workflow, issue types, JQL, project fields | forcing status into `open/closed` |
| Confluence | page hierarchy, page versions, storage format | treating a page tree as a flat issue list |

Every projection is a `RemoteBinding` with a sync base; inline comments are
projections of `SourceAnchor` (`model.spl:45-54`) re-anchored per patchset
(doc 2 §8.2 priority: entity id, syntax node, context fingerprint, line as
display fallback). A low-confidence re-anchor is shown as outdated, never
attached to the wrong code.

### Adapter structure

```text
src/app/devhub/provider/<name>/
  capabilities.spl   fn <name>_capabilities() -> ProviderCapabilities
  review.spl         struct <Name>Review  impl ReviewProvider
  task.spl           struct <Name>Task    impl TaskProvider      (omit if task.* is -)
  knowledge.spl      struct <Name>Wiki    impl KnowledgeProvider (omit if knowledge.* is -)
  release.spl        struct <Name>Release impl ReleaseProvider   (omit if release.* is -)
```

Adapters are structs holding a transport handle (composition); they normalize
provider payloads into lifecycle values and return `LifecycleResult`. Credential
material stays in the transport (`adapter_*.spl`, `auth.spl`) and never
appears in a lifecycle record, command JSON, or audit payload. Providers are
registered in a registry keyed by `provider_id`; adding one must not touch
`cmd_*.spl` or any Spipe skill (Stage 6a exit criterion).

### Provider contract suite (doc 1 §18.4, doc 2 §17.5)

One shared spec body, `test/01_unit/app/devhub/provider_contract/contract_body.spl`,
driven per provider by `<name>_spec.spl` against a recorded-fixture transport
(no network in unit tests). Every provider runs every case; a case a provider
does not support must return `PROVIDER_UNSUPPORTED` and is asserted as such —
it is never skipped:

1. capability discovery equals the declared record;
2. create / fetch / update review round-trip preserves `RevisionId` alias;
3. patchset race: `expected_revision` mismatch yields `SJ_REMOTE_STALE`-class
   rejection, no write;
4. idempotent replay: same `idempotency_key` twice produces one remote write;
5. inline thread publish / reply / resolve where `inline_threads`;
6. verdict projection respects `verdict_model` (Gerrit label fixture, Review
   Board ship-it fixture, GitLab no-request-changes strict-refusal fixture);
7. approval import binds to exact revision;
8. close / abandon;
9. task create / plan-apply where `task.*`;
10. pagination/cursor, rate-limit retry, auth expiry, network interruption;
11. webhook duplicate and out-of-order delivery through the outbox;
12. remote deletion / tombstone;
13. structured error normalization (every failure is a `LifecycleResult` with
    a stable `code`).

Verdicts: a provider spec run that executed zero contract cases is
`ERROR — nothing was checked`; any silent-success on an unsupported case is
`FAIL`. Stage 6a exit for a provider = all thirteen cases PASS or
explicitly-unsupported, no provider name appearing under `.spipe/` or
`.claude/skills/`.

## Policy compilation (Stage 6b)

`.spipe/policy/*.sdn` is normative. `spipe policy check/compile/explain/audit`
generates or verifies human/agent rules, skill contracts, guide tables, and gate
entries. It fails closed on missing commands/gates, drift, contradictory field
authority, or protected paths lacking independent enforcement.

## Failure and recovery behavior

- Persist an operation after every durable boundary.
- Make provider requests idempotent and remote writes optimistic-concurrency
  checked.
- Retain recovery refs for partial publication.
- Report backend alias/tree drift through SCV doctor.
- A break-glass request requires authority, reason, expiry, audit event, and a
  reconciliation incident; it can never manufacture valid release evidence.

## Performance and observability

Protected integration may scan only policy-declared changed scope unless a
profile explicitly requires full-tree evidence. Cache gate results solely by
exact revision, tool, policy, and environment digests. Record phase timing,
cache hit/miss, gate counts, CAS conflicts, provider retries, and max RSS.

Initial budgets are measurement gates, not guessed hard failures: record warm
DevHub command latency, review-open latency, SJ dry-run planning latency, and
integration overhead on realistic repository fixtures before setting release
thresholds.

That is deliberate (NFR-005). The measurement that must exist before any
threshold is written:

| Metric | Command | Fixture | Repeat |
|---|---|---|---|
| warm DevHub command latency | `devhub lifecycle inspect <domain> <id> --json` | this repo, `.scv/lifecycle` with >= 1,000 records | 10 runs, report median + p95 |
| review-open latency | `devhub review open <change>` (Stage 2) | a 50-file / 2,000-line change on this repo | 10 runs |
| SJ dry-run planning latency | `sj integrate <change> --dry-run --explain` | same change, full push-tier gate manifest | 10 runs |
| integration overhead | wall time of the nine planner steps minus gate execution time | same change | 5 runs |
| max RSS | every row above | `/usr/bin/time -v` | with each run |

Each measurement records binary identity (`readlink -f bin/simple` + size +
mtime, per `.claude/rules/commands.md`) and lands under
`doc/10_metrics/app/devhub/lifecycle_latency_<date>.md`. Thresholds are then
set from those numbers (proposed: p95 x 1.5 as the perf-regression gate) and
pinned by a fail-closed check script; a threshold with no metrics file behind
it is a defect. Until then the perf gate reports `ERROR — nothing was checked`,
never PASS.

## Security boundaries

Credential handling stays in provider transports and must never enter SCV
objects, command JSON, audit payloads, or remote URLs. Protected mutations need
explicit authority. Release publication requires a complete exact-revision gate
bundle, independent approval policy, deterministic identities, CAS, and no
unresolved critical finding.

## Compatibility strategy

Existing commands remain wrappers until parity tests prove typed equivalents.
Observe/shadow modes precede mutation authority. The initial implementation
does not change content authority, public refs, release publication, or provider
behavior by default.
