<!-- codex-research -->
# SCV–Jujutsu–Git Unified Release, Review, and Work-Item Design

**Target projects:** `ormastes/simple`, `ormastes/Spipe`  
**Date:** 2026-08-25  
**Status:** research, architecture, detailed design, process rules, and implementation plan

> **Filing note (2026-09-05):** companion to
> `scv_jj_git_devhub_spipe_unified_lifecycle_full_2026-08-25.md`. That document
> is the DevHub/Spipe-centric lifecycle view; this one is the
> release/review/work-item view and carries the `dev` gateway proposal, the
> authority-mode taxonomy (A/B/C), the SCV tag defects, and the release-unit
> (monorepo) model. Where they overlap they agree; where this one is more
> specific — tag immutability defects, release units, authority modes — it is
> the operative text.

---

## 1. Executive decision

Use the three systems for different responsibilities rather than treating them as interchangeable VCS implementations:

| System | Primary responsibility now | Long-term responsibility |
|---|---|---|
| **Jujutsu (`jj`/`sj`)** | Local change editing: automatic working-copy commit, stable change identity, stacking, split/squash/rebase, workspaces, operation-log recovery | Optional high-productivity frontend while its backend contract is compatible; otherwise its workflow is reproduced by SCV commands |
| **Git/GitHub** | Canonical recovery history, public interoperability, CI, remote hosting, pull requests, immutable public tags/releases | Public compatibility/export protocol and forge transport; it remains independently reconstructable even after SCV becomes authoritative |
| **SCV** | Shadow exact-byte store, implicit snapshots, parser/semantic indexes, gates, checkpoints, backend differential verification | Canonical local change/review/release/work-item graph, semantic review anchors, release provenance, offline-first collaboration, and generated Git mirrors |
| **Spipe** | Development-phase orchestration and agent skills | Provider-neutral workflow and policy engine above SCV/JJ/Git, review servers, issue trackers, and wikis |
| **`dev` tool/plugin** | New component | One command and API surface for local/remote change, review, work item, release, wiki, and provider synchronization |

The most important invariant is:

> **Exactly one authority may publish a mutable repository state in a workspace.** Other backends are transactional mirrors, validators, or adapters—not independent writers.

For the current SCV stabilization period, the authority is **Git/GitHub**, local editing is **Jujutsu**, and SCV remains a **shadow system**. This matches the repository's existing migration strategy. SCV should not become authoritative merely because more features have been implemented; promotion requires recovery, crash, divergence, and sustained shadow-operation evidence.

The recommended development model is trunk-based without long-lived feature branches:

- A developer's `jj` working-copy change is an unnamed descendant of `main`.
- The protected `main` bookmark does **not** move on every edit.
- Local review operates on that descendant before moving local `main`.
- Remote review uses a generated, short-lived transport bookmark such as `review/<actor>/<stable-change-id>`.
- Public/shared `main` moves only through the configured landing policy.
- Release branches exist only just in time for maintained release lines, not for ordinary feature development.

---

## 2. Current-state audit

### 2.1 SCV is already a real VCS subsystem

The current SCV implementation is much larger than an MVP design note. It already contains:

- byte-addressed content, file, tree, commit, change, and operation objects;
- working-copy snapshots, automatic snapshots, status, logs, and operation restoration;
- parser registries, parser indexes, syntax/semantic diff infrastructure;
- compile/test/public-ready state gates;
- merge and conflict objects;
- bookmarks and tags;
- Git fast-import export/import;
- packs, private synchronization, public filesystem remotes, and network remotes;
- checkpoints, `doctor`, integrity verification, and Git-vs-SCV backend comparison.

Therefore, this project should add a **workflow/control plane and first-class release/review/work-item objects**, not duplicate Git's branch commands one by one.

### 2.2 The current authority policy is already conservative

The SCV migration documentation explicitly makes GitHub/Git the recovery authority and SCV a shadow system during stabilization. It defines staged promotion from read-only observation through dual-write verification to eventual native authority. This is the correct safety posture and should remain normative.

### 2.3 Concrete SCV release gaps

The current tag implementation is not yet suitable as a release authority:

1. `scv_tag_set` replaces an existing tag with the same name. A published release tag must instead be immutable.
2. Bookmark updates create an operation and roll back on failure; tag updates currently do not have equivalent operation-log publication semantics.
3. The tag implementation writes `meta/tags`, while checkpoint source selection refers to `meta/tags.sdn`. This can omit tags from checkpoints.
4. Annotated-tag identity is stored separately, but a release needs a single verified object connecting version, source commit, evidence, artifact manifest, signatures, and publication records.
5. There is no first-class release-line, release-candidate, backport, support-window, or compatibility-decision object.

These are release-blocking correctness issues, not cosmetic CLI gaps.

### 2.4 Spipe's VCS and ship rules have drifted from `simple`

The `simple` repository's VCS rule says that raw `jj git push` must not be used because it bypasses the repository's required wrapper-level gates. The only documented landing path is `scripts/check/land.shs`.

The Spipe VCS and Ship documents still show raw `jj bookmark set main ... && jj git push ...`. The Ship phase then invokes PR creation/review **after pushing `main`**. Consequently, the documented remote review cannot protect the commit that was already published. The Ship document also references "3-Level Review wiring," but repository search finds no separate authoritative definition of that wiring.

This must be corrected before adding more review automation.

### 2.5 The current release skill is a version-bump script, not a release manager

The existing `/release` skill:

- updates four hard-coded version locations;
- creates a changelog skeleton;
- commits and creates a Git tag;
- asks before pushing;
- documents deleting the GitHub release and tag as rollback.

Required changes:

- determine version intent from public API/ABI and explicit release policy, not only a user-supplied bump word;
- review and land the release change before creating the final tag;
- create an RC and verified release object before stable promotion;
- treat a published version/tag as immutable;
- "rollback" a published release by revoking/yanking it and publishing a corrected version, not by silently repointing or deleting its identity;
- support independently versioned release units in the large `simple` monorepo.

### 2.6 Task and review integrations are provider-specific dispatchers

`/repo_and_pull_req` currently names GitHub, Jira, and Confluence directly. `/bug_review` joins GitHub Issues and Jira, but there is no canonical local work-item object, robust bidirectional event synchronization, conflict policy, or provider capability model. The default continuous mode of `spipe_loop` is also documented as unimplemented.

The redesign should preserve these commands as compatibility aliases while moving implementation to provider-neutral `/review`, `/work`, `/release`, and `/vc` domain services.

---

## 3. Research conclusions

### 3.1 Jujutsu is well suited to local change manipulation

Jujutsu changes can retain a stable change ID while commit hashes evolve, bookmarks map to Git branches for transport, and modifying operations are recorded in an operation log. This makes it a strong frontend for local stacked work and recovery. It also means that a stable logical change should be mapped to remote patch-set/revision identities rather than equated with one Git commit hash.

A colocated Jujutsu/Git repository automatically imports Git-side changes, but concurrent or independent rewriting can create divergent changes. The proposed gateway must therefore serialize mutations and record mappings; "both tools can see the same repository" is not equivalent to "both may mutate it concurrently without policy."

### 3.2 Trunk-based development fits the existing no-long-lived-branch rule

Trunk-based guidance supports either release directly from trunk or a just-in-time release branch. A release branch should be cut only when needed, receive selected fixes, and eventually be retired. Branches can be created retroactively from the exact historical revision, so speculative long-lived release branches are unnecessary.

For `simple`, this implies:

- ordinary work remains as small JJ/SCV changes based on `main`;
- remote review branches are ephemeral transport refs, not development authorities;
- maintained release lines use `release/<unit>/<major>.<minor>` only while supported;
- a fix is developed and reviewed on `main` first, then explicitly backported when applicable;
- a release branch is not merged wholesale back into `main`.

### 3.3 Small, self-contained changes improve review

Modern code-review research and industrial guidance consistently support small, self-contained changes. They are easier to understand and review thoroughly, and empirical work connects review coverage, participation, and expertise with post-release quality. Review tools must therefore optimize for change understanding, not just display a line diff.

SCV's parser-aware indexes can improve this by adding:

- semantic entity summaries;
- call/dependency impact;
- API/ABI changes;
- moved/renamed entity identity;
- generated-code suppression;
- inter-patchset semantic deltas;
- test and specification traceability.

### 3.4 Semantic version numbers are claims that need evidence

Semantic Versioning defines MAJOR/MINOR/PATCH in terms of public API compatibility and states that released contents must not be modified. Empirical studies show that version numbers frequently fail to signal real breaking changes. Therefore, SCV should not infer SemVer solely from commit-message prefixes.

A release plan should combine:

1. parser-derived public API/ABI comparison;
2. package/dependency graph impact;
3. deprecation and migration metadata;
4. explicit release-manager intent;
5. consumer compatibility tests where available;
6. an auditable override reason when the chosen version differs from automated evidence.

### 3.5 Review providers share concepts but not identical capabilities

GitHub, GitLab, Gerrit, and Review Board all expose programmatic review interfaces, but their models differ:

- GitHub centers review on pull requests, checks, protected branches/rulesets, and merge queues.
- GitLab exposes merge requests, approvals, merge controls, issues, and cross-references through APIs.
- Gerrit has stable Change-Ids, numbered patch sets, labels, and submit requirements.
- Review Board exposes review requests, diffs, published/draft reviews, replies, and diff comments.

The integration must not reduce everything to the lowest common denominator. It should define a stable core and negotiate optional capabilities.

### 3.6 Local-first work items are feasible

GitHub, GitLab, and Jira expose issue/work-item APIs, while tools such as `git-bug` demonstrate distributed offline-first issue objects. SCV can implement a stronger version because it already has immutable objects, operations, packs/remotes, and parser-aware links. Local state should be authoritative for offline edits, with provider mappings and an outbox/inbox synchronization protocol.

### 3.7 Model escalation must be evidence-driven and bounded

Research on model routing/cascades supports escalating uncertain cases to stronger models. However, current code-review agents remain incomplete: a 2026 code-review benchmark reports that evaluated agents collectively solve only about 40% of its tasks and often notice different aspects than human reviewers. The process must therefore combine deterministic checks, multiple review perspectives, and human authority for high-risk cases.

A stronger model should not be called merely because a weaker model emits the phrase "low confidence." Escalation should use structured signals, disagreement, evidence quality, code risk, and bounded recursion.

---

## 4. Authority modes

### 4.1 Mode A — `git_jj_scv_shadow` (use now)

```text
Authoritative published bytes/history : Git + GitHub
Local editing and stack manipulation   : Jujutsu
Shadow snapshots/semantic metadata     : SCV
Workflow and policy                    : Spipe/dev gateway
```

Rules:

- All mutations start through `dev` or an approved repository wrapper.
- `jj` may manipulate local changes.
- Git is used directly only for read-only inspection or explicitly wrapped compatibility operations.
- SCV records snapshots, mappings, gates, review/work-item events, and backend comparisons.
- SCV failure may reduce semantic/offline history but must not make published Git history unrecoverable.
- Publication uses the repository's configured landing wrapper; for `simple`, that is `scripts/check/land.shs`, not raw `jj git push`.

### 4.2 Mode B — `dual_verified`

```text
Git/JJ transaction  ─┐
                     ├─ gateway journal → compare trees/parents/refs → publish
SCV transaction     ─┘
```

Every operation has:

- an idempotency key;
- pre-state Git commit/ref, JJ operation/view, and SCV operation/view;
- intended logical change IDs;
- write-ahead transaction record;
- post-state mappings;
- exact-byte and parent/ref verification;
- rollback/recovery state.

No public push occurs until the differential verifier passes.

### 4.3 Mode C — `scv_native`

```text
SCV canonical objects/change/review/work/release graph
              │
              ├── generated Git mirror → GitHub/GitLab/Gerrit/CI
              ├── SCV native remote
              └── optional JJ frontend/adapter
```

Promotion requirements must include the existing SCV recovery criteria plus release/review/work-item-specific tests. A custom JJ storage backend should not be an early dependency. First use stable ID mappings and a gateway; consider a native backend only after its integration contract, crash semantics, and upstream maintenance cost are acceptable.

### 4.4 Forbidden configuration

Do not permit this topology:

```text
raw git mutation ─┐
raw jj mutation  ─┼─ independently update refs and metadata in one workspace
raw scv mutation ─┘
```

The gateway should detect `.git`, `.jj`, and `.scv`, acquire a workspace lease, select the configured authority mode, and reject unsupported raw mutation paths when enforcement is enabled.

---

## 5. Role matrix: SCV vs JJ vs Git

| Capability | Git | Jujutsu | SCV target |
|---|---|---|---|
| Public ecosystem and forge compatibility | **Primary** | Uses Git backend/transport | Export/import adapter |
| Automatic working-copy tracking | No | **Primary** | Add native implicit snapshots |
| Stable logical change identity across rewrite | Convention/tool-specific | **Primary** | **Primary**, mapped to JJ/Gerrit IDs |
| Operation-log undo | Reflog/plumbing, less unified | **Primary** | **Primary** |
| Stacked change editing | Manual/rebase tooling | **Primary** | Add first-class stack operations |
| Exact-byte immutable object storage | **Primary/mature** | Backend-dependent | Implemented, continue hardening |
| Parser-aware semantic indexes | External tools | External tools | **Primary** |
| Local review objects and threads | External tools/files | External tools | Add first-class objects |
| Offline work items | External tools | External tools | Add first-class objects |
| Release objects and provenance | Tags plus external release data | Git-compatible tags | Add first-class release graph |
| CI/remote review interoperability | **Primary** | Pushes Git refs | Provider adapters |
| Recovery authority today | **Primary** | Independent operation recovery | Shadow/checkpoint |
| Recovery authority after native promotion | Compatibility mirror | Optional frontend | **Primary** |

---

## 6. Branch, bookmark, stack, and release-line rules

### 6.1 Terminology

Use these terms consistently:

- **Change**: stable logical unit of work that can evolve through patch sets.
- **Commit revision**: one immutable content/parent realization of a change.
- **Stack**: ordered dependent changes, each independently reviewable when possible.
- **Bookmark/ref**: movable pointer used for integration or transport.
- **Tag**: immutable named release anchor.
- **Release line**: maintained ancestry for a supported major/minor family.
- **Patch set**: one review-visible revision of a stable change.
- **Work item**: feature, bug, task, research item, or code-quality item.

Do not call every JJ change a branch. Do not call an ephemeral PR transport ref a long-lived feature branch.

### 6.2 Main/trunk policy

1. `main` is the only permanent development bookmark.
2. `main` must be releasable according to the configured gate class.
3. A working-copy change is created on top of `main`; `main` remains at the last landed revision.
4. Changes should be self-contained and small enough for a reviewer to understand without reconstructing unrelated work.
5. Incomplete long-running features use feature flags, branch-by-abstraction, interfaces, or a reviewable stack—not a months-long branch.
6. Generated artifacts are reviewed through source generator changes and deterministic output checks, not giant undifferentiated diffs.

### 6.3 Local-main fast lane

For the user's desired small-change workflow:

```text
main(local) ── A working-copy change ── optional dependent change
                    │
              local review object
                    │
        static/tests + model escalation
                    │
             atomic local land
                    ▼
                main(local)'
```

This is "work directly from main" while preserving a meaningful review boundary. The local `main` pointer moves only after review passes.

Policy classes:

| Class | Example | Local review | Remote review | Human requirement |
|---|---|---:|---:|---:|
| R0 | comments, generated metadata with verified source | deterministic checks | optional | no |
| R1 | small docs/test-only/low-risk tooling | strong local model + checks | optional in solo repo; required in shared protected repo | policy-dependent |
| R2 | normal implementation | local review | required before shared `main` | one qualified reviewer or equivalent policy |
| R3 | public API, storage format, compiler/runtime, concurrency | multi-dimension local review | required | independent qualified reviewer |
| R4 | trust/signing, release pipeline, security boundary, mission-critical code | independent local reviewers + full gates | required | two-party/human sign-off |

A model review is evidence, not an identity-bearing human approval unless policy explicitly defines an automated reviewer role for that risk class.

### 6.4 Remote review transport refs

Generate refs only when publishing review:

```text
review/<actor>/<change-id>
review/<actor>/<change-id>/ps/<n>       # optional provider/mirror ref
stack/<actor>/<stack-id>/<position>     # only when provider requires stacked refs
```

Rules:

- generated from stable IDs, not titles;
- safe provider-specific encoding;
- owned by the gateway;
- deleted after merge/abandon plus retention period;
- never used as release authority;
- remote provider IDs are mappings, not the canonical change ID.

### 6.5 Release lines

Default:

```text
main
  ├── v2.4.0
  ├── v2.4.1
  └── current development
```

Create a release line only when an older family must continue receiving fixes:

```text
release/compiler/2.4
release/scv/1.1
release/os/0.8
```

Rules:

1. Cut just in time from an exact reviewed commit or final release tag.
2. Develop fixes on `main` first unless the defect is impossible/not applicable there.
3. Backport with an explicit backport object that records original change, selected destination, transformed patch if any, and verification evidence.
4. Never merge the whole release line back into `main`.
5. Do not place new general features on a maintenance line.
6. Retire the movable release-line ref after support ends; retain immutable tags and release objects.

### 6.6 Monorepo versioning

`simple` contains products with different compatibility and release cadences. Introduce **release units**:

```text
compiler
language-spec
runtime
stdlib
scv
simple-os
riscv-core
office
enterprise
spipe
```

Each unit declares:

- version scheme (`semver`, `calver`, internal build number);
- public API/ABI surface;
- dependency constraints on other units;
- release channel and support policy;
- artifact builders;
- required gates and reviewers.

A synchronized product release may compose several unit releases in a `version_set` object. Do not force every subproject to change version because one unit changed unless product policy requires lockstep releases.

---

## 7. Release architecture

### 7.1 Release state machine

```text
planned
  → candidate
  → verified_candidate
  → approved
  → published
  → supported
  → end_of_support

Exceptional side states:
  rejected | superseded | revoked | yanked
```

`published` is immutable. Corrections create a new version. `revoked` or `yanked` adds metadata and warnings without rewriting the source identity.

### 7.2 First-class SCV release object

Conceptual schema:

```text
Release
  release_id
  release_unit
  version
  scheme
  channel                 # alpha | beta | rc | stable | lts
  source_change
  source_commit
  source_tree
  parent_release
  release_line
  compatibility
    declared              # patch | backward_compatible | breaking
    detected_api
    detected_abi
    override_reason
  work_items[]
  changes[]
  backports[]
  gate_evidence[]
  review_approvals[]
  artifact_manifest
  sbom
  source_provenance
  build_provenance
  signatures[]
  publication_records[]
  created_at
  published_at
  state
```

The release object is immutable after publication. New evidence is appended as signed events referencing it.

### 7.3 Release-plan object

Before modifying versions, run `dev release plan`:

```text
ReleasePlan
  base_release
  target_source
  included_changes
  excluded_changes
  candidate_version
  compatibility_evidence
  dependency_updates
  changelog_sections
  migration_notes
  gate_plan
  artifact_plan
  reviewer_plan
  unresolved_questions
```

The version bump is an output of this plan and an explicit approval, not the first action.

### 7.4 Release process

1. **Plan** — select release unit, base release, target source, included work items, and compatibility evidence.
2. **Review plan** — resolve breaking-change classification, dependencies, migration text, and release-line need.
3. **Create release change** — update version metadata/changelog using generated source of truth; no final tag yet.
4. **Local review** — run release-specific local checks and higher-tier review.
5. **Remote review and land** — use the normal protected-main process.
6. **Build candidate** — build from a pinned landed source revision with reproducibility inputs.
7. **Verify candidate** — artifact tests, SBOM/provenance, installation/upgrade/rollback tests, API/ABI checks.
8. **Approve** — required people/roles sign the release object.
9. **Publish atomically** — create immutable SCV release/tag, export immutable Git tag, publish artifacts, verify each remote, append publication receipts.
10. **Observe** — health checks and release monitoring.
11. **Correct** — revoke/yank metadata if needed and issue a new version; never silently replace published bytes.

### 7.5 Tag rules

Replace `tag-set` semantics with:

```text
scv tag create <name> <commit> --annotated <object> --sign
scv tag verify <name>
scv tag list
scv tag revoke <name> --reason <work-item>   # metadata only
```

Rules:

- create fails if the name exists;
- no generic force-update for published namespaces;
- local disposable candidate refs use bookmarks, not tags;
- final and RC tags are operation-logged and checkpointed;
- tag, annotation, release object, source commit/tree, and signatures are checked together;
- Git export verifies that the exported tag resolves to the mapped Git commit;
- protected tag namespace policy applies remotely.

### 7.6 Version decision engine

Inputs:

- semantic public API diff;
- ABI/layout/calling-convention diff where applicable;
- language/spec grammar diff;
- serialized/storage/protocol format diff;
- dependency graph changes;
- behavior-contract tests;
- deprecation policy;
- declared work-item impact;
- human override.

Outputs:

```text
recommended: major | minor | patch | none
confidence: 0..1
reasons[]
breaking_entities[]
affected_consumers[]
required_migrations[]
override_required: bool
```

Fail closed for a stable release when analysis was required but did not run. "No evidence" is not "no breaking change."

### 7.7 Reproducibility and provenance

Record:

- exact source tree and release object;
- builder identity and workflow source;
- dependency lockfiles/toolchain versions;
- external build parameters;
- deterministic timestamp input such as `SOURCE_DATE_EPOCH`;
- artifact digests;
- SBOM and attestations;
- mapping from SCV release to Git tag and provider release ID.

The release verifier checks that the artifact came from an expected protected branch/tag and expected build configuration.

---

## 8. Unified local and remote review model

### 8.1 Domain entities

```text
Change
PatchSet
ReviewRequest
DiffAnchor
Thread
Comment
Finding
CheckRun
Approval
SubmitRequirement
ReviewStack
ProviderMapping
ArtifactLink
WorkItemLink
```

Core invariants:

- one stable `change_id`, many immutable patch sets;
- a patch set names exact source/target trees and commits;
- review comments anchor to semantic identity when available, then content-range identity, then a line fingerprint fallback;
- every approval applies to a specific patch set and policy revision;
- a new material patch set invalidates approvals according to policy;
- remote review state is synchronized through events, not overwritten wholesale;
- provider-specific features remain accessible through capabilities/extensions.

### 8.2 Review anchor design

Anchor priority:

1. semantic entity ID + field/path inside the entity;
2. syntax node ID + raw content ID;
3. before/after context fingerprint + path lineage;
4. line range as display fallback.

Example:

```text
DiffAnchor
  file_id: file_...
  entity_id: entity_...
  syntax_path: fn[hash_file]/branch[error]
  base_content: sha256_...
  head_content: sha256_...
  context_before: sha256_...
  context_after: sha256_...
  display_line: 182
```

When a patch set changes, SCV reanchors automatically and records confidence. A low-confidence reanchor is shown as outdated/unresolved rather than silently attached to the wrong code.

### 8.3 Normalized provider adapter

Core interface:

```text
provider.detect_capabilities()
review.create(change, patchset, target)
review.update(review_id, patchset)
review.fetch(review_id, cursor)
review.comment(review_id, anchor, body)
review.reply(thread_id, body)
review.resolve(thread_id)
review.submit_verdict(review_id, verdict, evidence)
review.get_requirements(review_id)
review.merge_or_submit(review_id, expected_patchset)
review.close(review_id, reason)
```

Capabilities:

```text
patchsets
stacked_changes
inline_comments
suggested_edits
thread_resolution
draft_reviews
labels_or_votes
required_approvals
merge_queue
submit_requirements
code_owners
webhooks
wiki_links
issue_links
```

Adapters:

- `local_scv`
- `github`
- `gitlab`
- `gerrit`
- `review_board`
- later: Bitbucket, Azure DevOps, Phabricator-compatible endpoints, email/patch series, ForgeFed federation.

### 8.4 Local review workflow

```text
dev review open --local --change @
dev review run --level auto
dev review show
dev review fix <finding-id>
dev review rerun --changed-only
dev review approve --role automated-reviewer
dev land --local
```

The local review uses exactly pinned committed content. It must never analyze a shared mutable working tree while reporting a verdict for another revision.

### 8.5 Remote review workflow

```text
dev review publish --provider auto --target main
dev review sync
dev review run --remote --changed-only
dev review reply <thread>
dev review submit
```

Publication steps:

1. verify local review object and gates;
2. generate transport bookmark/ref;
3. push through the provider-aware gate wrapper;
4. create or update remote review;
5. record provider IDs and exact patch-set mapping;
6. import remote checks/comments/approvals;
7. re-run local policy over the combined state;
8. submit through merge queue/provider submit operation;
9. fetch and verify landed commit/tree;
10. delete/retire transport refs.

### 8.6 Stack-aware review

A review stack is an ordered DAG, normally linear:

```text
A: data model
B: parser support depends on A
C: UI depends on B
```

Rules:

- each change has its own acceptance criteria and review;
- a provider without native stacks receives generated dependent PRs/branches;
- rebasing a lower change updates descendants and patch-set mappings atomically;
- review UI shows both per-change diff and cumulative diff;
- landing is bottom-up unless provider supports an equivalent atomic stack submission;
- a semantic change in A invalidates impacted approvals in B/C based on dependency analysis, not necessarily every unrelated approval.

---

## 9. Recursive higher-model review

### 9.1 Review pipeline

```text
Pinned patch set
   │
   ├─ deterministic gates: parse/build/test/lint/security/policy
   ├─ semantic impact extraction
   ├─ Tier-1 model reviewers by dimension
   ├─ finding verifier/adjudicator
   └─ escalation router → stronger model / independent model / human
```

Review dimensions:

- correctness;
- error handling and recovery;
- concurrency/memory safety;
- security/trust boundary;
- performance and resource behavior;
- API/ABI/spec compatibility;
- storage/protocol migration;
- tests and observability;
- architecture and dependency direction;
- documentation and traceability.

### 9.2 Structured finding contract

Every model finding must contain:

```text
Finding
  finding_id
  patchset
  category
  severity
  anchor
  claim
  evidence
  execution_or_reproduction
  expected_behavior
  suggested_action
  confidence
  uncertainty_reasons[]
  reviewer_model
  reviewer_policy_version
  status
```

A vague concern without an anchor or falsifiable explanation is advisory noise, not a blocking finding.

### 9.3 Escalation conditions

Escalate when any condition holds:

- risk class requires a stronger reviewer;
- confidence is below the policy threshold;
- two reviewers disagree materially;
- a finding is severe but lacks executable evidence;
- the change touches trust/signing, unsafe/FFI, concurrency, compiler lowering, storage recovery, public API/ABI, or release machinery;
- semantic impact exceeds the reviewed scope;
- tests/static analysis disagree with the model;
- the reviewer explicitly abstains with a typed reason;
- a previous high-severity comment remains unresolved;
- the same model authored the code and independence is required.

### 9.4 Bounded recursive delegation

A higher model may ask another reviewer only through a recorded sub-review request:

```text
SubReview
  parent_review
  question
  scope
  requested_dimension
  required_evidence
  model_tier
  budget
  depth
  deadline_or_cycle_limit
```

Defaults:

- maximum depth: 3;
- maximum fan-out: one reviewer per unresolved dimension, configurable;
- no delegation to an equal/weaker tier unless seeking independent diversity;
- repeated question/hash is deduplicated;
- every escalation records why the previous level was insufficient;
- budget exhaustion yields `abstain/needs-human`, never an automatic pass;
- critical findings require independent confirmation or deterministic evidence;
- final policy evaluation is separate from all reviewer models.

### 9.5 Verdicts

```text
pass
pass_with_advisories
changes_requested
blocked_by_checks
abstain_needs_stronger
abstain_needs_human
invalid_review
```

The final gate consumes findings, checks, approvals, risk class, and provider state. A reviewer model never directly moves `main` or publishes a release.

---

## 10. Local and remote work-item model

### 10.1 Canonical work item

```text
WorkItem
  work_id                  # stable UUID/content-independent logical ID
  kind                     # feature | bug | task | research | code_quality
  title
  description
  state
  priority
  risk
  owners[]
  acceptance_criteria[]
  dependencies[]
  children[]
  related_changes[]
  reviews[]
  target_release[]
  artifacts[]              # specs, plans, reports, wiki/docs
  phase_state
  external_links[]
  created_at
  updated_at
```

State machine:

```text
proposed → refined → researched → designed → specified → implementing
  → verifying → local_review → remote_review → release_ready → released → done

Side states: blocked | deferred | rejected | duplicate | superseded
```

### 10.2 Source of truth

Long term:

- immutable SCV work-item events are canonical;
- a materialized local index accelerates queries;
- `.spipe/work/<id>/state.sdn` is a structured projection/cache;
- `.spipe/work/<id>/state.md` and feature documents are generated human/LLM views;
- remote issues/work items are mapped replicas.

This replaces "Markdown state file is the sole communication channel" without removing readable state documents.

### 10.3 Event-sourced synchronization

Events:

```text
work_created
field_changed
criterion_added
criterion_verified
dependency_added
comment_added
state_transitioned
change_linked
review_linked
release_linked
external_mapping_added
external_event_imported
conflict_recorded
```

Sync components:

- durable outbox with idempotency keys;
- per-provider cursor/watermark;
- ETag/version or updated-at preconditions;
- provider webhook ingestion plus polling reconciliation;
- event-origin identifiers to prevent loops;
- field-level conflict policy;
- append-only comments rather than destructive merge;
- explicit manual resolution for conflicting state transitions.

### 10.4 Provider mappings

```text
ProviderMapping
  local_id
  provider
  repository_or_project
  remote_type
  remote_id
  remote_url
  remote_version
  last_in_cursor
  last_out_event
  capabilities
  state
```

Support first:

1. GitHub Issues/sub-issues/projects links;
2. GitLab issues/work items;
3. Jira issues/links/remote links;
4. GitHub/GitLab wiki and Confluence as linked artifact projections;
5. later distributed SCV native federation.

### 10.5 Feature-document integration

A feature document is an artifact generated from the work-item graph:

```text
research → requirements → architecture → design → plan → implementation
    → tests/evidence → review → release notes
```

Each document section has stable semantic IDs. Renames/moves update links through the document compiler/index. Remote wiki pages store a provider mapping and source hash; edits import as events or create a reviewable document change rather than silently overwriting local source.

---

## 11. Provider-neutral `dev` tool

### 11.1 Architecture

```text
CLI / TUI / IDE / Spipe skills / MCP
                 │
             dev service
                 │
 ┌───────────────┼────────────────────────────────────────┐
 │ domain        │ policy          │ sync/event engine    │
 │ change/review │ release/work    │ outbox/inbox/webhook │
 └───────┬───────┴────────┬────────┴───────────┬───────────┘
         │                │                    │
   VCS adapters      review adapters      task/wiki adapters
 SCV/JJ/Git          local/GH/GL/Gerrit   GH/GL/Jira/wiki
```

The service returns typed SDN/JSON. Human CLI/TUI and LLM output are renderings of the same result, preventing each skill from parsing ad hoc prose.

### 11.2 Core commands

```text
dev status

dev change new --work <id>
dev change describe <text>
dev change split
dev change squash
dev change rebase --onto main
dev change abandon
dev change stack

dev review open [--local] [--target main]
dev review run [--level auto|1|2|3] [--changed-only]
dev review show
dev review publish [--provider auto|github|gitlab|gerrit|review-board]
dev review sync
dev review resolve <thread>
dev review submit

dev land --local
dev land --remote

dev work new|show|edit|link|sync|close
dev work import <provider-id>

dev release plan --unit <unit>
dev release candidate <version>
dev release verify <release-id>
dev release promote <release-id> --channel stable
dev release backport <change> --to <line>
dev release revoke <release-id> --reason <work-id>

dev recover
dev doctor
dev compare-backends
```

### 11.3 VCS command dispatch

Mode-specific adapters implement one interface:

```text
status()
snapshot()
new_change(parent)
describe(change, message)
split(change, selection)
squash(source, destination)
rebase(change_or_stack, destination)
restore(operation)
resolve_revision(selector)
create_transport_ref(change)
push_transport_ref(ref, provider)
land(review, expected_revision)
create_release_tag(release)
verify_mappings()
```

The user and skills do not need to remember which operation belongs to SCV, JJ, or Git.

### 11.4 Repository-specific landing policy

The gateway loads a repository profile:

```text
land:
  command: sh scripts/check/land.shs
  supports_review_ref: false     # current script pushes main only
  requires_committed_content: true
```

The implementation should extend the landing wrapper to support:

```text
land.shs --target-ref refs/heads/review/<id> --base origin/main --tip <sha>
land.shs --submit-review <provider-review-id>
```

Do not bypass current guards while introducing remote review. Generalize the guard wrapper instead.

---

## 12. Required SCV feature work

### P0 — correctness before release use

1. Fix `tags` vs `tags.sdn` path inconsistency.
2. Make protected tags immutable and operation-logged.
3. Include tag and annotated/release objects in checkpoints, packs, fsck, GC reachability, import/export, and backend verification.
4. Add an atomic ref transaction and compare-and-swap precondition.
5. Add namespace policy for `main`, `release/**`, `review/**`, and `v*`.
6. Add Git/JJ/SCV mapping integrity checks.
7. Add a workspace mutation lease and transaction journal.

### P1 — logical changes, patch sets, and stacks

1. Strengthen change objects with stable external mapping IDs and predecessor/successor relations.
2. Add immutable patch-set objects.
3. Add first-class stack objects and stack rewrite mapping.
4. Export/import stable change trailers where useful without making commit-message text the only identity store.
5. Map SCV change IDs to JJ change IDs, Gerrit Change-Ids, Git commits, and provider review revisions.

### P2 — local review

1. Review request, thread, comment, finding, check, approval, and policy-evaluation objects.
2. Parser-aware stable anchors and reanchoring.
3. Inter-patchset raw/syntax/semantic diff.
4. Local review TUI/CLI and machine-readable output.
5. Model review evidence and bounded escalation graph.
6. Approval invalidation based on patch-set materiality.

### P3 — work items and documents

1. Work-item and event objects.
2. Dependency/sub-item graph.
3. Acceptance-criterion evidence links.
4. Feature-document projections and stable section IDs.
5. Outbox/inbox and provider mapping store.
6. GitHub/GitLab/Jira adapters.

### P4 — release management

1. Release unit and version-set configuration.
2. API/ABI/spec/storage compatibility diff.
3. Release plan, candidate, release, publication, revoke/yank, and backport objects.
4. Immutable release tags and signatures.
5. Artifact manifest, SBOM, source/build provenance, and remote receipts.
6. Support-window/release-line policy.
7. Reproducibility verification.

### P5 — provider review adapters

1. GitHub PR/check/ruleset/merge-queue adapter.
2. GitLab MR/approval adapter.
3. Gerrit change/patch-set/label/submit-requirement adapter.
4. Review Board review-request/diff/comment adapter.
5. Capability negotiation and contract tests.
6. Webhook service plus polling reconciliation.

### P6 — native authority promotion

1. Full multi-backend fault injection.
2. Bidirectional mirror reconstruction.
3. SCV-native remote review/work-item sync.
4. Git mirror generation from release/review refs.
5. Promotion gates matching the existing S0–S6 migration plan.

---

## 13. Spipe rule and skill redesign

### 13.1 Replace contradictory VCS instructions

One generated VCS policy must feed:

- `simple/.claude/rules/vcs.md`;
- `Spipe/.claude/agents/vcs.md`;
- `/sync`, `/ship`, `/release`, `/repo_and_pull_req` compatibility skills;
- Codex/Gemini/Claude generated variants;
- `dev` runtime policy.

No prose-only rule may claim enforcement without a machine-readable gate row and executable contract test.

### 13.2 Preserve SStack phases but change the gates

Minimal-compatible eight-phase process:

| Phase | New responsibility |
|---|---|
| 1 Dev | Create/link canonical work item; refine goal/ACs/risk/release target |
| 2 Research | Research with source/evidence links |
| 3 Architecture | Architecture and affected release units |
| 4 Spec | Failing specs and compatibility checks |
| 5 Implement | Small stable changes/stacks |
| 6 Refactor | Cleanup and split oversized review changes |
| 7 Verify | Deterministic gates **plus local review and model escalation** |
| 8 Submit | Publish remote review if required, synchronize comments, satisfy policy, land, verify remote result, generate report |

`/release` is a separate post-land release pipeline. Do not combine ordinary feature submission with creation of a public release tag.

### 13.3 Replace current Ship ordering

Old documented order:

```text
commit → push main → create/review PR → report
```

New order:

```text
freeze patch set
→ local review/gates
→ publish ephemeral review ref
→ remote review/checks
→ submit/merge queue or approved landing wrapper
→ fetch and verify main
→ completion report/work-item transition
```

For a policy-allowed local-only fast lane:

```text
freeze → local high-tier review/gates → atomic local land
→ repository landing wrapper → verify remote main
```

### 13.4 New skills

- `/vc`: authority-mode detection, status, change/workspace operations, synchronization, recovery.
- `/review`: local/remote review using one domain model and model escalation.
- `/work`: local/remote feature/bug/task management and feature-document projection.
- `/release`: release plan/candidate/verification/promotion/backport/revoke.
- `/ship`: compatibility alias for `/review submit` followed by work-item completion; never create a final release.
- `/repo_and_pull_req`: deprecated compatibility dispatcher to `/review` and `/work` adapters.
- `/bug_review`: compatibility view over `/work --kind bug`.

### 13.5 Continuous synchronization

Implement the currently missing default `spipe_loop` mode as an event-driven reconciler:

1. process local outbox;
2. ingest provider webhooks/events;
3. poll providers whose webhook coverage is incomplete;
4. reconcile review/work/release mappings;
5. detect stale patch sets, approval invalidation, failed checks, and remote edits;
6. update generated state/dashboard documents;
7. notify only actionable transitions;
8. never mutate code or land changes without a separately authorized command.

---

## 14. Policy defaults

### 14.1 Change-size policy

Use adaptive limits rather than one universal LOC number:

- target one logical purpose;
- warn when unrelated semantic entities or release units are mixed;
- suggest split when reviewer context exceeds configured file/entity/LOC thresholds;
- exclude generated output only when its generator and deterministic comparison are included;
- allow mechanical migrations with a machine-verifiable transformation plan and sampled human/model review;
- block a change whose review description cannot state one coherent purpose.

A starter repository policy may choose numeric warnings, but they are local policy—not research constants.

### 14.2 Review independence

- The authoring agent/model cannot be the sole approving reviewer for R2+.
- R3 uses an independent strong model plus qualified human or explicit owner policy.
- R4 requires human two-party approval and signed policy override for exceptions.
- A higher model may delegate investigation but cannot delegate final policy authority.

### 14.3 Fail-closed verdicts

Use the repository's existing three-way discipline:

```text
PASS       exit 0, non-vacuous evidence count
FAIL       exit 1, checked and found a violation
ERROR      exit 2, nothing trustworthy was checked
```

No empty diff, missing executable, API outage, unsupported provider capability, or model timeout may become an implicit pass.

### 14.4 Raw command policy

- Read-only raw `git`, `jj`, and `scv` commands are allowed for diagnosis.
- Mutating raw commands are allowed only in explicitly documented recovery mode.
- Normal mutation uses `dev`/repository wrappers.
- Recovery operations record before/after IDs and run backend comparison.
- Provider writes use idempotency keys and expected-version preconditions.

---

## 15. Implementation architecture and file plan

### 15.1 `simple` SCV modules

Proposed modules:

```text
src/lib/scv/transaction.spl
src/lib/scv/backend_mapping.spl
src/lib/scv/ref_policy.spl
src/lib/scv/patchset.spl
src/lib/scv/stack.spl
src/lib/scv/review.spl
src/lib/scv/review_anchor.spl
src/lib/scv/review_policy.spl
src/lib/scv/work_item.spl
src/lib/scv/work_event.spl
src/lib/scv/release_unit.spl
src/lib/scv/release_plan.spl
src/lib/scv/release.spl
src/lib/scv/backport.spl
src/lib/scv/provenance.spl
src/lib/scv/provider_mapping.spl
src/lib/scv/sync_outbox.spl
```

Modify:

```text
src/lib/scv/refs.spl
src/lib/scv/stabilize.spl
src/lib/scv/integrity*.spl
src/lib/scv/pack*.spl
src/lib/scv/public_remote.spl
src/lib/scv/network_remote.spl
src/lib/scv/fast_import*.spl
src/app/scv/main.spl
```

### 15.2 `dev` tool modules

```text
src/app/dev/main.spl
src/lib/dev/domain.spl
src/lib/dev/policy.spl
src/lib/dev/vc_gateway.spl
src/lib/dev/review_service.spl
src/lib/dev/work_service.spl
src/lib/dev/release_service.spl
src/lib/dev/sync_service.spl
src/lib/dev/provider_capability.spl
src/lib/dev/provider/github*.spl
src/lib/dev/provider/gitlab*.spl
src/lib/dev/provider/gerrit*.spl
src/lib/dev/provider/review_board*.spl
src/lib/dev/provider/jira*.spl
```

Keep providers dynamically loadable so adding a provider does not rebuild the core workflow unnecessarily.

### 15.3 Spipe files

```text
doc/00_llm_process/skill_command/skills/pipe/vc/skill.md
doc/00_llm_process/skill_command/skills/pipe/review/skill.md
doc/00_llm_process/skill_command/skills/pipe/work/skill.md
doc/00_llm_process/skill_command/skills/pipe/release/skill.md
doc/00_llm_process/skill_command/skills/pipe/ship/skill.md
.claude/skills/lib/dev_workflow.md
config/dev/workflow_policy.sdn
config/dev/providers.sdn
```

Generate provider/model-specific skill variants from these sources rather than editing copies independently.

---

## 16. Parallel-agent implementation plan

### Agent A — VCS authority and transaction layer

Owns:

- authority-mode detection;
- workspace lease;
- write-ahead transaction;
- Git/JJ/SCV mappings;
- compare-and-swap ref publication;
- recovery and differential verification.

Must land before provider writes or SCV release refs.

### Agent B — SCV ref/tag correctness

Owns:

- tag path correction;
- immutable tags;
- operation-log semantics;
- checkpoint/pack/fsck/GC reachability;
- protected namespaces;
- tests for duplicate/repoint/recovery cases.

### Agent C — change, patch-set, stack model

Owns:

- stable change enhancements;
- immutable patch sets;
- stack graph and rewrite mappings;
- JJ/Gerrit/Git identity mapping;
- interdiff primitives.

### Agent D — local review and semantic anchors

Owns:

- review/thread/comment/finding objects;
- parser-aware anchors and reanchoring;
- raw/syntax/semantic interdiff;
- local CLI/TUI.

Depends on C and existing parser/diff capsules.

### Agent E — review policy and model cascade

Owns:

- risk classifier;
- deterministic check aggregation;
- structured finding contract;
- reviewer independence;
- bounded escalation router;
- policy verdict engine;
- model benchmark/regression corpus.

### Agent F — work items and feature documents

Owns:

- work-item/event graph;
- acceptance criteria and phase mapping;
- state SDN/Markdown projections;
- document/section stable IDs;
- dependency and release links.

### Agent G — release/version/provenance

Owns:

- release units/version sets;
- compatibility analysis;
- release plan/candidate/final objects;
- backport graph;
- reproducible build/provenance manifests;
- publication/revoke/yank flows.

Depends on B, C, D/E policy evidence, and F work-item links.

### Agent H — provider abstraction and GitHub first adapter

Owns:

- capability model;
- review/work provider interfaces;
- GitHub PR/review/check/issue adapter;
- webhooks, cursor, idempotency, and contract fixtures;
- merge-queue integration.

### Agent I — GitLab/Gerrit/Review Board/Jira/wiki adapters

Owns one provider per isolated lane. Each uses the same conformance suite and cannot modify core domain schemas without architecture review.

### Agent J — Spipe skills and migration

Owns:

- new `/vc`, `/review`, `/work`, `/release`, `/ship` sources;
- SStack phase changes;
- legacy alias routing;
- single generated policy source;
- dashboards and continuous reconciler behavior.

### Agent K — verification and fault injection

Owns independently:

- property tests;
- crash points;
- provider API replay fixtures;
- synchronization conflict tests;
- tag/release immutability tests;
- model recursion bounds;
- end-to-end current-mode and dual-mode scenarios.

This agent must not share implementation ownership with the component it verifies.

---

## 17. Verification matrix

### 17.1 VCS invariants

- one active writer lease;
- exact Git/JJ/SCV tree equality when mappings claim equality;
- parent graph mapping is complete;
- no lost/duplicated change after split/squash/rebase;
- operation undo yields a valid old or new state;
- interrupted provider push is retryable and idempotent;
- raw unauthorized push is detected by policy/audit where enforceable;
- no vacuous pass.

### 17.2 Tag/release invariants

- duplicate protected tag creation fails;
- published tag cannot move;
- tag survives checkpoint/restore/pack/import;
- SCV tag maps to exact Git tag commit;
- release object maps to exact source tree and artifact digests;
- RC-to-stable promotion does not rebuild from a different unreviewed source unless policy explicitly creates a new candidate;
- revocation does not rewrite release identity;
- backport records original and transformed changes.

### 17.3 Review invariants

- comment remains on the intended semantic entity after line movement;
- uncertain reanchor becomes outdated, not silently wrong;
- approval names patch set and policy version;
- material patch-set update invalidates required approvals;
- local and remote comments converge without duplication;
- model recursion terminates at configured depth/budget;
- abstention cannot become pass;
- author model cannot self-approve above allowed risk;
- provider submit uses expected revision and rejects race/stale patch set.

### 17.4 Work-item sync invariants

- offline edits replay idempotently;
- webhook and poll duplicate events collapse;
- comments are not lost under concurrent edits;
- conflicting state transitions create an explicit conflict;
- remote deletion/permission loss does not delete canonical local history;
- feature documents are reproducible projections;
- change/review/release links remain traceable after remote ID changes.

### 17.5 Provider conformance

Every adapter must pass fixtures for:

- capability discovery;
- create/update/fetch review;
- patch-set race;
- inline comment/reply/resolve where supported;
- approval/requirement import;
- close/abandon;
- create/update work item;
- pagination/cursors;
- rate limit/retry;
- authentication expiration;
- network interruption;
- idempotent replay;
- unsupported capability fail-closed behavior.

---

## 18. Migration sequence

### Stage 0 — repair policy drift

- Update Spipe VCS/Ship to use repository landing policy.
- Remove push-main-before-review ordering.
- Make `/release` distinguish candidate, publication, and revocation.
- Add tests that compare generated skill commands with repository VCS policy.

### Stage 1 — gateway in read/plan mode

- Implement `dev status`, mode detection, capability detection, mapping display, and dry-run plans.
- No new write path yet.

### Stage 2 — local review and work-item store

- Add SCV review/work objects in shadow mode.
- Generate existing `.spipe` state documents from structured objects.
- Run model review without granting landing authority.

### Stage 3 — GitHub review/work sync

- Publish ephemeral review refs through generalized repository gates.
- Create/sync PRs and issues.
- Keep GitHub/Git authoritative.

### Stage 4 — release objects in shadow mode

- Produce release plans, compatibility evidence, candidate manifests, and provenance alongside existing Git releases.
- Compare and audit without changing release authority.

### Stage 5 — dual-verified transactions

- Every reviewed/landed/released operation writes Git/JJ and SCV records and passes backend comparison.
- Exercise crash and remote-failure tests.

### Stage 6 — additional providers

- GitLab, Gerrit, Review Board, Jira, and wiki adapters through conformance tests.

### Stage 7 — native authority evaluation

- Apply the existing S5/S6 promotion requirements.
- GitHub remains an independently verifiable mirror and recovery path.

---

## 19. Immediate rule changes

1. Replace "no branches" with **"no long-lived feature branches; ephemeral provider transport bookmarks and maintained release lines are allowed only through `dev`."**
2. Replace all raw Spipe `jj git push` instructions with the repository-selected landing adapter.
3. Move remote review before shared-main publication.
4. Treat local `main` as protected by a local review transaction even in a solo workflow.
5. Split `/ship` from `/release`.
6. Make published tags/releases immutable; replace destructive rollback with revoke/yank plus corrective release.
7. Make structured work/review/release objects canonical and Markdown/wiki pages projections.
8. Require pinned committed content for all gates and model reviews.
9. Require bounded recursive model escalation with typed abstention.
10. Keep SCV non-authoritative until the existing stabilization promotion criteria pass.

---

## 20. Recommended first implementation slice

The first coherent vertical slice should be small but end-to-end:

```text
Work item
  → JJ change on main descendant
  → SCV shadow patch set
  → deterministic local gates
  → structured strong-model local review
  → generated GitHub review ref/PR
  → comment/check synchronization
  → approved provider submit
  → fetch/verify main
  → SCV mapping + work-item completion
```

Limit the first slice to GitHub and current `git_jj_scv_shadow` mode. Do not simultaneously implement native SCV authority, five providers, and full release publication. Once this slice is correct, release candidates reuse the same review, policy, provider, mapping, and evidence infrastructure.

---

## 21. Research sources

### Official specifications and product documentation

- Semantic Versioning 2.0.0 — https://semver.org/
- Jujutsu glossary, tutorial, operation log, bookmarks, architecture, and GitHub workflow — https://jj-vcs.github.io/jj/latest/
- Trunk-Based Development release guidance — https://trunkbaseddevelopment.com/
- GitHub pull request, branch protection, ruleset, merge queue, and Issues APIs — https://docs.github.com/
- GitLab Merge Requests and Issues APIs — https://docs.gitlab.com/api/
- Gerrit Changes REST API and change/patch-set model — https://gerrit-review.googlesource.com/Documentation/
- Review Board Web API — https://www.reviewboard.org/docs/manual/latest/webapi/
- Jira Cloud REST API — https://developer.atlassian.com/cloud/jira/platform/rest/v3/
- SLSA source requirements and threats — https://slsa.dev/spec/
- Reproducible Builds `SOURCE_DATE_EPOCH` specification — https://reproducible-builds.org/specs/source-date-epoch/
- Google Engineering Practices code-review guide — https://google.github.io/eng-practices/review/

### Research papers and empirical evidence

- Sadowski et al., *Modern Code Review: A Case Study at Google* (2018).
- McIntosh et al., *An Empirical Study of the Impact of Modern Code Review Practices on Software Quality* (2016).
- Bacchelli and Bird, *Expectations, Outcomes, and Challenges of Modern Code Review* (2013).
- Rigby and Bird, *Convergent Contemporary Software Peer Review Practices* / review knowledge diffusion research.
- Li et al., *A Large-Scale Empirical Study on Semantic Versioning in the Golang Ecosystem* (ASE 2023).
- Ochoa et al., *Breaking bad? Semantic versioning and impact of breaking changes in Maven Central* (2022).
- Zhang et al., *Code Review Agent Benchmark (c-CRAB)* (2026).
- Moslem et al., *Dynamic Model Routing and Cascading for Efficient LLM Inference* survey (2026).

### Relevant offline-first precedent

- `git-bug`, distributed offline-first issue objects embedded in a Git repository — https://github.com/git-bug/git-bug
