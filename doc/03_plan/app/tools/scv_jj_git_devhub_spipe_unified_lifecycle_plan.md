<!-- codex-design -->
# Unified lifecycle implementation plan

**Status (measured 2026-09-05, revised same day after Stage 0.5 partial landing):**
Stage 0.5 items 1, 3 and 4 landed; item 2's gate-manifest/CAS half and item 5
(reachability guard) remain open. The library is no longer dormant: `bin/sj plan`
reaches the typed layer and `devhub lifecycle record-change` persists through
`lifecycle_store_write`. Still true: no protected-ref mutation path, no remote
provider, and **0 of 18 acceptance criteria hold an authoritative PASS** (the
deployed `bin/simple` is still the Rust seed). No stage is promoted.

> **Same-session supersession.** The "Measured reality" section below was written
> against the pre-landing tree earlier on 2026-09-05 and is retained as history.
> Claims later work invalidated are marked SUPERSEDED inline with the disproving
> evidence; nothing there was deleted.
**Research (authority):**
`doc/01_research/app/tools/scv/scv_jj_git_devhub_spipe_unified_lifecycle_full_2026-08-25.md`
(the 165-line `..._2026-08-25.md` is its summary) and
`doc/01_research/app/tools/scv/scv_jj_git_unified_release_review_work_item_2026-08-25.md`.
**Design:** `doc/05_design/app/tools/scv_jj_git_devhub_spipe_unified_lifecycle.md`
**Acceptance:** `scv_jj_git_devhub_spipe_unified_lifecycle_acceptance.md` (same dir);
AC-1..AC-18 are defined only in
`.spipe/scv_jj_git_devhub_spipe_unified_lifecycle/state.md:17-34` (phase
`agent-base-delivered-unverified`, `:63`).

## Measured reality

Feature code is 1,985 lines: `src/lib/scv/lifecycle/` (11 files, 896),
`src/app/sj/{operation,integrate_plan,gate_manifest,lifecycle_policy}.spl`
(626), `src/app/devhub/{cmd_lifecycle,version_manifest,provider/lifecycle_*}.spl`
(463). The other 83 files / 19,322 lines under `src/lib/scv` are pre-existing SCV,
not this feature. The value objects, codecs, parsers and planners are real and
unstubbed (zero TODO/FIXME). Nothing drives them:

- ~~`src/app/sj/main.spl:5-8` imports only `app.sj.client`; the typed operation
  layer is unreachable from `bin/sj`.~~ **SUPERSEDED 2026-09-05:** `bin/sj plan
  <legacy-argv>` routes `legacy_argv_operation` -> `vcs_operation_valid` ->
  `plan_integration` and prints a dry-run plan (`src/app/sj/plan_main.spl`,
  `bin/sj`). `sj git push` was deliberately NOT intercepted — that spelling is
  `land.shs`'s. `main.spl` keeps its `app.sj.client`-only import ON PURPOSE:
  `use` resolves eagerly (strace: 4 `scv/lifecycle` opens per `sj --help` with
  the import present, 0 without), so importing the planner there would put the
  lifecycle graph on every push.
- `src/app/sj/integrate_plan.spl` and `gate_manifest.spl` have no production
  caller. `scripts/check/land.shs` never references them: it runs two rules.sdl
  checks (`:72,:77`) and raw `git push origin refs/heads/$WORK_BRANCH` (`:100`),
  then prints that protected integration "remains a separate reviewed CAS
  operation" (`:101`) — an operation that has no executor.
- `lifecycle_store_write` (`src/lib/scv/lifecycle/store.spl:20`) is called only
  from `lifecycle_persist_sync_conflict` (`sync.spl:75`) and one unit spec;
  that function itself has zero `src/app` and zero `test/` callers.
  `lifecycle_gate_bundle_admits` (`review.spl:57`) has no `src/` caller. No lifecycle record is ever persisted by a
  command.
- `src/app/devhub/provider/lifecycle_provider.spl:9-30` declares five traits
  (`LifecycleProvider`, `ReviewProvider`, `TaskProvider`, `KnowledgeProvider`,
  `ReleaseProvider`) with zero implementers.
- `devhub lifecycle` (`src/app/devhub/main.spl:99-100` →
  `cmd_lifecycle.spl`) exposes read-only `capabilities`/`inspect` over six
  domains (`:60,:71,:88,:130`); ~~`dry-run` unconditionally returns
  `DRY_RUN_INPUT_REQUIRED`, exit 2.~~ **SUPERSEDED 2026-09-05:** `dry-run` reads
  the persisted envelope and emits `"status":"planned"` (`cmd_lifecycle.spl:113-130`),
  fail-closed on `DRY_RUN_INPUT_REQUIRED` / `DOMAIN_UNSUPPORTED` /
  `DRY_RUN_RECORD_ABSENT` / `LIFECYCLE_STORE_INTEGRITY`. `record-change`
  (`:99-109,:200-222`) is the first production caller of `lifecycle_store_write`;
  `LocalScvProvider` (`provider/lifecycle_local.spl`) is the first
  `LifecycleProvider` implementer (the other four traits still have none).
- Absent entirely: SARIF, finding reanchor, webhooks/CloudEvents transport, mock
  reviewer tiers, policy compiler, GitHub/GitLab/Gerrit projection,
  `SCV-Change-Id` trailer, live CAS/publish, signed tags, wiki sync.
- Evidence: 15 executable specs, none skip-tagged, all diagnostic only because
  `bin/simple --version` still reports the Rust bootstrap seed. The two generated
  manuals `doc/06_spec/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle{,_acceptance}_spec.md`
  are STALE (their `Source SHA-256` rows, `_spec.md:199` / `_acceptance_spec.md:103`,
  record `9ef67837…`/`03bb52a6…`; current sources hash `a801dcb0…`/`389cd10b…`);
  regenerate with `bin/simple spipe-docgen` once an
  admitted pure-Simple CLI exists.

## Delivery rule

Each stage is a separate logical change, defaults to observe/dry-run, and
preserves Git/JJ recovery authority until its exit gate passes. A stage is
promoted by measured exit evidence, never because code exists. Every gate and
guard emits the repo verdict convention — last stdout line `PASS — <n> …
checked` (n > 0) exit 0 / `FAIL — …` exit 1 / `ERROR — nothing was checked`
exit 2 — and a 0-item run is ERROR. Shared IDs, enums, capabilities, command
registry, policy schemas and fixtures keep one merge owner.

Authority modes (research 2 §4) gate the spine: Stages 0–6 run in Mode A
`git_jj_scv_shadow`; Stage 7 requires Mode B `dual_verified` evidence before
Mode C `scv_native` is considered; the §4.4 topology (raw git/jj/scv mutation in
one workspace) is forbidden at every stage. Research 2 §18 orders provider sync
before release objects; this plan keeps research 1 §19's Phase 0–7 order, which
the existing code and AC numbering already follow.

## Stage 0 — protected-ref safety

Source-complete: `.spipe/policy/vcs.sdn` + observe-only parser
(`src/app/sj/lifecycle_policy.spl`, 364 lines); gate manifest model
(`src/app/sj/gate_manifest.spl`). Unwired: nothing invokes the manifest against
pinned BASE/HEAD; `land.shs --dry-run` (`:94-97`) does not route through a
typed planner. Absent: conformance matrix for every protected-update spelling.

1. Keep the protected class list (`main`, `integration/main`, `release/*`,
   candidate, tag, recovery, review refs) in `vcs.sdn` as the only source.
2. Make the gate manifest directly invocable against pinned BASE/HEAD
   (research 1 P0-1) with the PASS/FAIL/ERROR verdict.
3. Add the conformance matrix: every protected update spelling (`git push`,
   `jj git push`, `sj`, `land.shs`) is enumerated and either routed or refused.
4. Route `land.shs --dry-run` through `integrate_plan` and diff old/new plans.

Exit: no protected path reports success without complete gate evidence; a raw
update is detected and cannot create integration or release evidence.

## Stage 0.5 — wiring and reachability (BLOCKING, new)

The single largest gap: a delivered library nothing calls. No later stage may
start until this one exits.

1. **[LANDED 2026-09-05]** Producer: `bin/sj plan` argv → `legacy_argv_operation`
   → `vcs_operation_valid` → typed `VcsOperation` (AC-5). Implemented as a
   separate entry (`src/app/sj/plan_main.spl`, dispatched in `bin/sj`) rather
   than by changing `main.spl`'s import, because `use` is eager and `main.spl`
   is on the `land.shs` push path.
2. Executor: one `sj integrate --dry-run` path that builds `IntegrateRequest`,
   calls `integrate_plan`, evaluates `gate_manifest`, and calls
   `lifecycle_gate_bundle_admits`; prints the plan, mutates nothing.
3. **[LANDED 2026-09-05]** Persistence: `lifecycle_store_write` has a `src/app`
   caller (`cmd_lifecycle.spl:99-109`) with a proven write/read-back round trip.
   The pre-landing audit claim "only a unit spec calls it" was imprecise:
   `sync.spl:75` called it, but that function had no `src/app` or `test/` caller.
4. **[LANDED 2026-09-05]** `devhub lifecycle dry-run` accepts real input
   (`cmd_lifecycle.spl:113-130`) instead of always returning
   `DRY_RUN_INPUT_REQUIRED`.
5. Reachability guard `scripts/check/check-lifecycle-reachability.shs`
   (fail-closed, `--selftest`): FAIL when any exported symbol in
   `src/lib/scv/lifecycle/**`, `src/app/sj/{operation,integrate_plan,gate_manifest}.spl`
   has zero non-test callers; ERROR when 0 symbols scanned.

Exit: `sj integrate --dry-run` on a real change produces one typed plan and one
persisted audit record from an unmodified `bin/sj`; the reachability guard
reports `PASS — <n> symbol(s) checked, 0 unreachable`; AC-5 flips from
"not wired" to diagnostic PASS.

## Stage 1 — lifecycle identity shadowing

Source-complete: ChangeId/RevisionId/alias derivation
(`src/lib/scv/lifecycle/identity.spl`, `model.spl`, `entity_codec.spl`).
Unwired: no JJ/Git import produces an identity; no fsck/doctor check. Absent:
`SCV-Change-Id` trailer export.

1. Import JJ change/commit and Git OID aliases on every `sj` observe/snapshot
   without changing content authority (Mode A).
2. Export the `SCV-Change-Id` trailer as an interoperability aid only.
3. Add alias/tree-equivalence doctor checks and identity fsck.

Exit: every new JJ change has a stable SCV ChangeId and every snapshot maps to
verified SCV/JJ/Git identities across amend/rebase/export/import.

## Stage 2 — local review and integration

Source-complete: ReviewSession/Run, Finding, Approval, GateRun/GateBundle
(`review.spl`), exact-revision invalidation, typed `IntegrateRequest` planning
with CAS/lease intent (`integrate_plan.spl`). Unwired: nothing creates a review
or evaluates a bundle outside unit specs. Absent: anchor/reanchor, SARIF
import/export, mock reviewer tiers, live lease, live CAS, audit trail.

1. `sj review` creates ReviewSession/Run bound to an exact RevisionId; any
   rewrite marks approvals stale (research 1 P0-4).
2. Add parser-aware anchor/reanchor and SARIF import/export.
3. Add bounded mock reviewer tiers and the R0–R4 review-risk classes
   (research 2 §6.3 table; independence rules §14.2): R0 deterministic only; R1 strong local model; R2 local
   review + one qualified reviewer; R3 multi-dimension review + independent
   reviewer; R4 independent reviewers + full gates + two-party human sign-off.
   The authoring agent is never the sole approver for R2+.
4. Live lease, CAS and audit for `integration/main` only, after parity tests
   against the Stage 0.5 dry-run plans.

Exit: a local-only change is reviewed, escalated, approved, gated, and
race-safely integrated; concurrent candidates yield one CAS winner and one clean
retry; every approval carries session, revision, tree digest, policy digest and
evidence digest.

## Stage 3 — canonical version and release lifecycle

Source-complete: `release/version.sdn` checks (`version_manifest.spl`),
immutable release transitions (`release.spl`). Unwired: render/check/explain is
plan-only, no consumer migrated. Absent: everything below. The architecture doc
(37 lines) has no release/version section (3 incidental word hits) — an
architecture section is a prerequisite for 3.4–3.7.

1. Fix the four SCV tag defects (research 2 §2.3, P0) BEFORE any release
   object is trusted:
   - T-1 `scv_tag_set` (`src/lib/scv/refs.spl:77-100`) replaces an existing
     name in place (`:93-95`). Replace with `scv tag create` that FAILS if the
     name exists; no force-update for published namespaces.
   - T-2 tag updates create no operation-log entry and do not roll back, unlike
     bookmarks. Make final/RC tags operation-logged.
   - T-3 tags are written to `meta/tags` (`refs.spl:71-72`) while checkpoint
     and stabilize source selection read `meta/tags.sdn`
     (`src/lib/scv/maintenance.spl:571`, `stabilize.spl:21`), so tags drop out
     of checkpoints. Unify the path and add a fsck row.
   - T-4 no single verified release object links version, source
     commit/tree, gate bundle, artifact manifest, SBOM, provenance, signatures
     and publication records (research 2 §7.2). Add it, immutable after
     publish.
2. Add release units and version sets for the monorepo (research 2 §6.6):
   each unit (`compiler`, `language-spec`, `runtime`, `stdlib`, `scv`,
   `simple-os`, `riscv-core`, `office`, `enterprise`, `spipe`) declares scheme,
   API/ABI surface, dependency constraints, channel/support policy, builders,
   gates and reviewers; a `version_set` composes unit releases; no lockstep bump
   unless product policy says so.
3. Release lines (research 2 §6.5): cut just in time from an exact tag,
   fix on `main` first, explicit backport object, never merge a line back.
4. ReleaseLine, ReleaseCandidate, Release, artifact and provenance links;
   candidate `abandon` vs published `withdraw`/`yank` (research 1 P0-3).
5. Structured version identity (`simple --version --json`, research 1 P0-5).
6. Signed annotated tag dry-run and Git object verification.
7. Migrate one version consumer, then the release skill, after parity.

Exit: a candidate is prepared and verified without hand edits;
version/source/artifact/provenance identity is queryable; published tags are
immutability-enforced by a fail-closed check that replays T-1..T-3 as fixtures.

## Stage 4 — DevHub provider projection (GitHub)

Source-complete: capability records (`lifecycle_capability.spl`), provider
traits (`lifecycle_provider.spl:9-30`), three-way sync planning and durable
conflict (`sync.spl`), `devhub/v1` output envelope. Unwired: zero trait
implementers; outbox identities are computed but never sent. Absent: RemoteBinding
registry, GitHub adapter, webhook/CloudEvents transport, idempotency store.

1. First `ReviewProvider`/`ReleaseProvider` implementer: GitHub, behind an
   experimental flag.
2. RemoteBinding registry and durable outbox with replay-safe identities.
3. Round-trip findings, threads, approvals, exact head and release metadata
   without semantic flattening; stale provider head is a structured refusal.

Exit: one local review projects to GitHub and returns with no duplicate
findings; stale provider heads are blocked; contract suite PASSes with n > 0.

## Stage 5 — features, tasks, and wiki

Source-complete: Feature/Task/Document objects (`work.spl`), feature manifest
separation. Absent: three-way Jira/GitHub task sync, Confluence/Git-wiki
managed regions, work-item event sourcing (research 2 §10.3), virtual views.

1. Event-sourced work items with outbox/inbox and provider mapping store.
2. Field-authoritative three-way task sync; conflicts persisted, never merged
   silently.
3. Managed-region wiki sync; `.spipe/run` state stays separate and is promoted
   only by checkpoint.

Exit: one feature links documents, tasks, changes, reviews and releases;
offline/remote concurrent edits produce explicit conflicts with no silent loss.

## Stage 6a — provider design (BLOCKING prerequisite, new)

No design exists for GitLab, Gerrit, Review Board or Bitbucket: the design doc
mentions none of them (0 hits), nor does the architecture doc. Stage 6
implementation may not start until a design section covers, per provider:
capability record, review/patch-set/label/submit-requirement mapping, semantic
gaps that must fail explicitly, auth/transport, pagination/ETag/rate-limit,
webhook + polling reconciliation, and the shared conformance suite (research 1
§18.4, research 2 §17.5).

Exit: design doc section reviewed by the merge owner; every provider row names
at least one explicit unsupported semantic.

## Stage 6 — provider expansion and policy compilation

Absent entirely: all four providers, policy compiler (research 1 §14.2),
generated skills/rules/guides.

1. GitLab, Gerrit, Review Board, then Bitbucket through the Stage 6a contract
   suite.
2. Policy compiler for review/release/version/task/provider/model/authority
   policies; drift fails CI.
3. Generate and verify Spipe skills, agent rules, guide tables and gates; keep
   compatibility aliases until structured-command parity passes.

Exit: unsupported semantics fail explicitly; provider logic does not leak into
Spipe; policy drift fails CI.

## Stage 7 — SCV content-authority promotion

Requires Mode B `dual_verified` (idempotency key, pre/post state for Git, JJ
and SCV, write-ahead record, byte/parent/ref verification, rollback) before Mode
C. Follow the existing SCV S0–S6 gates: dual-write equivalence, backup/restore,
fault injection, recovery, conservative GC, rollback proof.

Exit: only measured conformance promotes SCV from lifecycle authority to
content writer; Git/JJ rollback remains available until final approval.

## Stage ↔ REQ ↔ AC ↔ spec cross-walk

Status column is the 2026-09-05 measurement. "diag" = diagnostic PASS on the
Rust seed only, never authoritative.

| Stage | REQ | AC | Executable spec (`test/`) | Status |
|---|---|---|---|---|
| 0 | REQ-002, REQ-008, REQ-010 | AC-4 | `01_unit/app/sj/lifecycle_policy_plan_spec.spl` | diag; manifest not invocable |
| 0.5 | REQ-002, REQ-009 | AC-5, AC-7 | `01_unit/app/sj/legacy_argv_dry_run_plan_spec.spl` (6/6), `01_unit/app/devhub/lifecycle_record_store_spec.spl` (7/7), `01_unit/app/devhub/lifecycle_local_provider_spec.spl` (3/3) | AC-5 wired via `sj plan`; AC-7 has a local write path. Both diagnostic only — deployed `bin/simple` is the Rust seed. Items 2 and 5 open |
| 1 | REQ-001 | AC-1, AC-2 | `01_unit/lib/scv/lifecycle_entity_codec_spec.spl`, `lifecycle_identity_spec.spl`, `lifecycle_codec_spec.spl` | diag; no importer |
| 2 | REQ-003, REQ-002 | AC-3, AC-6 | `01_unit/lib/scv/lifecycle_review_sync_release_spec.spl`, `01_unit/app/sj/integration_policy_evidence_spec.spl`, `gate_manifest_spec.spl`, `03_system/app/scv/feature/..._lifecycle_spec.spl` | diag; no executor |
| 3 | REQ-006 | AC-9, AC-10 | `01_unit/app/devhub/version_manifest_spec.spl`, `lifecycle_review_sync_release_spec.spl` | diag; T-1..T-4 open, no arch |
| 4 | REQ-004, REQ-005 | AC-7, AC-8 | `lifecycle_command_spec.spl`, `lifecycle_review_sync_release_spec.spl` | diag; 0 provider impls |
| 5 | REQ-007 | AC-11 | `01_unit/lib/scv/lifecycle_work_spec.spl` | diag; no sync |
| 6a/6 | REQ-004, REQ-008, REQ-009 | AC-15, AC-17 | none | absent; no design |
| 7 | REQ-010, NFR-007 | AC-18 | none | blocked |
| all | — | AC-12, AC-13, AC-14, AC-16 | `03_system/app/scv/feature/..._acceptance_spec.spl` (trace inventory), stale manuals | AC-13/18 blocked on admitted CLI |

Sys-test plan rows (`doc/03_plan/sys_test/scv_jj_git_devhub_spipe_unified_lifecycle.md:8-14`)
cover REQ-001..010 + NFR-002/007 only; add rows for the NFRs below and one
fault-injection row (research 1 §18.7) when their owner stage lands.

## NFR ownership (no test rows today)

| NFR | Owner stage | Required evidence |
|---|---|---|
| NFR-001 Safety | 0.5 → 2 | executor refuses malformed identity, stale CAS/approval, vacuous evidence, unknown policy |
| NFR-003 Auditability | 0.5 | every persisted plan names actor, authority, revisions, policy/gate digests |
| NFR-004 Recovery | 2, 7 | fault injection after each durable boundary; idempotent replay |
| NFR-005 Performance | 0.5, 4 | no full-tree scan/reread/subprocess on `sj integrate --dry-run` or provider hot path; warm latency + max RSS recorded |
| NFR-006 Security | 4 | credentials never in objects, JSON, audit or URLs; negative fixture |
| NFR-008 Quality | every stage | 80% branch coverage, no vacuous assertion, files < 800 lines |

## Ownership lanes

| Lane | Scope | Deliverable |
|---|---|---|
| Wiring (Stage 0.5) | `src/app/sj/main.spl`, executor, reachability guard | reachable typed path + audit record |
| Schema/integration | shared IDs, enums, capabilities, policy versions, fixtures | stable contracts, merge ownership |
| SCV lifecycle + tags | `src/lib/scv/lifecycle/**`, `refs.spl`, `maintenance.spl` | identity, review, gate, release stores; T-1..T-4 |
| SJ gateway | `src/app/sj/**`, `land.shs` | typed operations, leases, CAS, gates, audit |
| Review | review library, DevHub review domain | state machine, anchors, SARIF, R0–R4 routing |
| DevHub providers | registry/adapters, sync commands | Stage 6a design, GitHub, binding/outbox |
| Version/release | `release/**`, DevHub release/version | release units, version sets, provenance |
| Feature/task/wiki | DevHub work/document domains | event-sourced items, three-way sync |
| Spipe policy | policy compiler, skills, guides | thin clients, drift gate |
| Verification | lifecycle/provider/fault-injection suites, manual regeneration | adversarial bypass and recovery evidence |

Sidecars only after the merge owner fixes interface, command, scenario-step,
checker-helper and fail-fast placeholder names.

## System-test plan

- Identity: rewrite/rebase/Git round-trip, alias recovery.
- Review: exact-revision invalidation, local-only flow, bounded escalation,
  self-approval denial per R2+, SARIF, reanchor.
- Integration: full gate enumeration, missing-hook safety, concurrent CAS,
  remote-head change, network interruption, break-glass audit.
- Tags/release: T-1..T-3 replay fixtures, projection drift, candidate abandon,
  immutable publication, digest/provenance mismatch, backport duty,
  withdraw/replace, version-set composition.
- Provider: discovery, pagination, idempotency, ETag conflict, auth/rate limit,
  duplicate/out-of-order webhook, tombstone, semantic gap.
- Fault injection: fail after each persistent boundary; prove idempotent,
  explainable recovery.

Executable specs land with their stage, never as passing placeholders; every
unresolved oracle stays `fail("unresolved unified lifecycle oracle")`.

## Verification gates

Per stage: run its acceptance evidence once; stop when green; at most three
fix/verify cycles. Before any promotion: an admitted pure-Simple `bin/simple`
(the seed's results are not production evidence), regenerated `doc/06_spec`
manuals, `sspec-maintain` and `duplicate-check` executed, direct env/runtime
audits, affected compiler/lib/MCP/LSP checks, structured perf evidence for hot
paths, and a full `$verify` `STATUS: PASS`.

## History

- 2026-08-25: observe-only base published to `main` as Git
  `5cd33eca7717a7b87856a001fdb4f72deacfe00d` via user-authorized `--no-verify`.
  That waiver is a publication fact, not a `STATUS: PASS` or gate receipt.
- 2026-09-05: audit found the base dormant (this document); prior header
  "Agent-base implementation delivered" withdrawn; AC-5 corrected to not wired.

## Next change

Stage 0.5 only: wire `bin/sj` to the typed operation layer, add the dry-run
executor and reachability guard, and re-run the focused specs once on an
admitted CLI. Do not combine wiring, evidence recovery, public-ref mutation, or
release publication in one change.
