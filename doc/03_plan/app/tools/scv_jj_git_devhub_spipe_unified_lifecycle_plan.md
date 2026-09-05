<!-- codex-design -->
# Unified lifecycle implementation plan

**Status (measured 2026-09-05, revised same day after Stage 0.5 partial landing):**
Stage 0.5 items 1, 3 and 4 landed; item 2 is PARTIAL (`sj plan` reaches
`plan_integration`, but the gate-manifest/CAS/bundle half has no executor) and
item 5 (reachability guard) is open. The library is no longer dormant: `bin/sj
plan` reaches the typed layer, and `devhub lifecycle record-change` persists
through `lifecycle_store_write`. Still true: no protected-ref mutation path, no
remote provider, and **0 of 18 acceptance criteria hold an authoritative PASS**
(the deployed `bin/simple` is still the Rust seed). No stage is promoted.
**Ceiling: "Stage 0.5 done" for this lane can only ever mean source-complete
with diagnostic evidence — never "verified" — until a non-seed `bin/simple` is
deployed.** Sequenced closure criteria: § "Path to Stage 0.5 done" below.
New same-day finding: the committed `.spipe/policy/vcs.sdn` is REJECTED by its
own canonical parser (see "Measured reality"), so the protected-target
predicate cannot be wired until that parse defect is fixed.

> **Same-session supersession.** The "Measured reality" section below was written
> against the pre-landing tree earlier on 2026-09-05 and is retained as history.
> Claims it makes that later work invalidated are marked SUPERSEDED inline with
> the disproving evidence; nothing there was deleted.
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

- ~~`src/app/sj/main.spl:5-8` imports only `app.sj.client`; `legacy_argv_operation`
  (`src/app/sj/operation.spl:38`) and `vcs_operation_valid` (`:28`) have no
  `src/` caller outside their own file. The typed operation layer is unreachable from `bin/sj`.~~
  **SUPERSEDED 2026-09-05:** `bin/sj plan <legacy-argv>` now routes through
  `legacy_argv_operation` -> `vcs_operation_valid` -> `plan_integration` and prints
  a dry-run plan (`src/app/sj/plan_main.spl`, `bin/sj:37-45`,
  `integrate_plan.spl:112,:137`). `sj git push` was deliberately NOT intercepted —
  that is `land.shs`'s path. `main.spl` keeps its `app.sj.client`-only import
  on purpose: `use` resolves eagerly (strace: 4 `scv/lifecycle` opens per
  `sj --help` when the import was present, 0 after), so a `plan` import there
  would put the lifecycle graph on every push.
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
  `DRY_RUN_INPUT_REQUIRED` (`:137-138`), exit 2.~~
  **SUPERSEDED 2026-09-05:** `dry-run` now reads the persisted envelope and emits
  `"status":"planned"` (`cmd_lifecycle.spl:113-130`), staying fail-closed on
  `DRY_RUN_INPUT_REQUIRED` / `DOMAIN_UNSUPPORTED` / `DRY_RUN_RECORD_ABSENT` /
  `LIFECYCLE_STORE_INTEGRITY`. `record-change` (`:99-109,:200-222`) is the first
  production caller of `lifecycle_store_write`, and `LocalScvProvider`
  (`provider/lifecycle_local.spl`) is the first `LifecycleProvider` implementer
  (was 0; the other four traits still have none).
- Absent entirely: SARIF, finding reanchor, webhooks/CloudEvents transport, mock
  reviewer tiers, policy compiler, GitHub/GitLab/Gerrit projection,
  `SCV-Change-Id` trailer, live CAS/publish, signed tags, wiki sync.
- Evidence: 15 executable specs, none skip-tagged, all diagnostic only because
  `bin/simple --version` still reports the Rust bootstrap seed. The two generated
  manuals `doc/06_spec/03_system/app/scv/feature/scv_jj_git_devhub_spipe_unified_lifecycle{,_acceptance}_spec.md`
  are STALE (their `Source SHA-256` rows, `_spec.md:201,:207` /
  `_acceptance_spec.md:103,:109` — re-measured 2026-09-05, the earlier `:199`
  cite had drifted — record `9ef67837…`/`03bb52a6…`; current sources hash
  `a801dcb0…`/`389cd10b…`); regenerate with `bin/simple spipe-docgen` once an
  admitted pure-Simple CLI exists.
- **Protected-ref policy: committed, parsed nowhere on the `sj` path, and
  rejected by its own parser (measured 2026-09-05).** Three separate facts,
  each of which an earlier framing got wrong:
  1. The policy IS committed: `.spipe/policy/vcs.sdn` (300 lines, schema
     `spipe-vcs/3`, tracked since `e274cd33719`, 2026-08-27). The comment at
     `src/app/sj/integrate_plan.spl:158-159` ("No committed protected-ref
     policy source exists in this tree") and the user-facing `bin/sj plan`
     output line at `:172` ("not consulted (no committed protected-ref policy
     source)") are both FALSE and must change with the wiring.
  2. It is unwired on the `sj` path: `plan_integration` is called with
     `protected_target` hardcoded `false` (`integrate_plan.spl:160`), so every
     `sj plan` is rejected `SJ_POLICY_TARGET` (`:36-37`). The reader exists
     elsewhere: `devhub lifecycle policy-check [path]` defaults to
     `.spipe/policy/vcs.sdn` (`src/app/devhub/cmd_lifecycle.spl:152-153` →
     `lifecycle_policy_json` `:65-71` → `parse_canonical_lifecycle_vcs_policy`,
     `src/app/sj/lifecycle_policy.spl:321`), and
     `src/app/release/session_authority.spl:200` binds the file's SHA-256.
  3. Wiring alone would NOT make the PASS branch reachable, because the
     committed file does not parse: `bin/devhub lifecycle policy-check` →
     `{"status":"rejected","code":"POLICY_INVALID","message":"unsupported or
     missing schema"}`, rc=1 (seed binary, diagnostic). Cause, proven by probe:
     `parse_lifecycle_vcs_policy` (`lifecycle_policy.spl:257-278`) is an
     indent-blind, last-wins line scan. Nested `schema:` lines at
     `vcs.sdn:181` (`spipe-review-admission/1`) and `:246`
     (`spipe-changed-path-manifest/1`) overwrite the header's `spipe-vcs/3`,
     which the parser explicitly accepts (`:282`). Deleting those two lines
     advances the rejection to `"recovery refs must be append-only"` (`:305`)
     — same defect: `update: deny` at `vcs.sdn:103,112` (under `authoring:`)
     overwrites the `recovery/*` clause's `update: append_only` (`:50`). No
     spec ever parses the committed file — `lifecycle_policy_plan_spec.spl:34-58`
     and `integration_policy_evidence_spec.spl` use inline payloads only —
     which is why this was invisible. Needs a `doc/08_tracking/bug/` record
     from the `src/app/sj` owner (not filed by this plan lane).
  Even after the parse fix and the wiring, `sj plan` still cannot reach PASS:
  the legacy path passes empty identities and an empty bundle (`:148-157`), so
  the next rejection is `SJ_IDENTITY_MISSING` (`:38-39`). PASS first becomes
  reachable only with the item-2 executor that builds a full `IntegrateRequest`.
  **Line-cite pin:** every `integrate_plan.spl` / `lifecycle_policy.spl` cite in
  this document is against the COMMITTED blob at `e6446521cd3`. The working
  tree copies were under concurrent, uncommitted edit by the `src/app/sj` lane
  while this was written (`integrate_plan.spl` +96/-9, `lifecycle_policy.spl`
  +24 vs HEAD at 2026-09-05; the WC already reads `.spipe/policy/vcs.sdn`), so
  WC line numbers differ and steps 1-2 of the path below may be landing.
  Re-measure against the next commit, not against the working tree.

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
   separate entry (`src/app/sj/plan_main.spl`, dispatched at `bin/sj:37-45`)
   rather than by changing `main.spl`'s import, because `use` is eager and
   `main.spl` is on the `land.shs` push path.
2. **[PARTIAL 2026-09-05]** Executor: one `sj integrate --dry-run` path that
   builds `IntegrateRequest`, calls `integrate_plan`, evaluates
   `gate_manifest`, and calls `lifecycle_gate_bundle_admits`; prints the plan,
   mutates nothing. Landed half: `sj plan` reaches `plan_integration`
   (`integrate_plan.spl:160`) and prints a rejected plan. Open half: no path
   builds a full `IntegrateRequest`, invokes `plan_protected_gate_manifest`
   (`gate_manifest.spl:76`) against pinned BASE/HEAD, or calls
   `lifecycle_gate_bundle_admits` (`src/lib/scv/lifecycle/review.spl:57`, still
   zero `src/` callers). See § "Path to Stage 0.5 done", steps 3.
3. **[LANDED 2026-09-05]** Persistence: `lifecycle_store_write` has a `src/app`
   caller (`cmd_lifecycle.spl:99-109`) and a proven write/read-back round trip.
   Note the pre-landing audit claim "only a unit spec calls it" was already
   imprecise: `sync.spl:75` called it, but that function itself had no
   `src/app` or `test/` caller.
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

## Path to Stage 0.5 done (sequenced 2026-09-05)

**Read this first, and read it literally.** The deployed `bin/simple` is
`bin/release/aarch64-unknown-linux-gnu/simple`, and `bin/simple --version`
prints the Rust bootstrap-seed warning (measured 2026-09-05). Under the repo
rule that the seed's results are not production evidence, **0 of 18 ACs can
hold an authoritative PASS on this machine, no matter what lands.** Every
"exit evidence" below is therefore *diagnostic* evidence (seed-run specs,
seed-run CLI output, static counts). "Stage 0.5 done" for this lane MEANS
"every IN item below is source-complete and its diagnostic evidence is
recorded". It NEVER means "verified", and a later session that reads a green
row here as verification is misreading this document. The one and only
promotion path is: deploy a self-hosted `bin/simple`, re-run the focused specs
once, and only then write "verified".

Two classes of item, deliberately kept apart:

- **Closable now** — pure-Simple source under `src/app/sj/**`,
  `src/app/devhub/**`, `src/lib/scv/lifecycle/**`, plus specs and shell guards;
  evidence is seed-diagnostic.
- **Blocked on a non-seed `bin/simple`** — anything whose exit evidence is the
  word "authoritative": AC PASS status, manual regeneration as a gate input,
  `$verify STATUS: PASS`.

Order is a dependency order, not a priority order; step *n* is a precondition
of step *n+1* where the "Depends" column says so.

| # | Item | Scope for 0.5 | Depends | Closable now? | Exit evidence (diagnostic; last stdout line is the verdict) |
|---|---|---|---|---|---|
| 1 | Fix the policy parser: `parse_lifecycle_vcs_policy` must be indent-aware (or scan only the `protected_refs:` block), so the committed `.spipe/policy/vcs.sdn` parses. `src/app/sj` lane. | IN — new, found 2026-09-05 | — | yes | `bin/devhub lifecycle policy-check` → `"status":"ok","schema":"spipe-vcs/3","protected_ref_count":7`, rc 0; one unit spec that parses the COMMITTED file by path (not an inline payload) and asserts `valid` + all seven `lifecycle_policy_ref` hits; the two existing negative fixtures (`lifecycle_policy_plan_spec.spl:34-42`) still reject; bug record filed with the two probe messages above as its reproducer. |
| 2 | Wire `sj plan` to the policy: replace the hardcoded `false` at `integrate_plan.spl:160` with `lifecycle_policy_ref(parse_canonical_lifecycle_vcs_policy(file_read(".spipe/policy/vcs.sdn")), target_ref)` non-nil; set `request.policy_digest` from the parsed digest; delete the false comment `:158-159` and the false output line `:172`. Another agent is doing this now — this row states the contract, it does not build it. | IN | 1 | yes | `bin/sj plan` on a protected spelling rejects with a code OTHER than `SJ_POLICY_TARGET` (expected: `SJ_IDENTITY_MISSING`, `:38-39`); on an undeclared ref still `SJ_POLICY_TARGET`; missing or invalid policy file → rejected, never admitted, and the printed policy line names the file and its digest. `legacy_argv_dry_run_plan_spec.spl` gains one fixture per branch. Wiring without step 1 would reject every ref as invalid policy and must not be called done. |
| 3 | Item-2 executor (`sj integrate --dry-run`): builds a full `IntegrateRequest` (change/revision/base ids, expected+observed remote revision, policy digest, gate profile, actor, authority), plans the manifest with `plan_protected_gate_manifest` against pinned BASE/HEAD from the `tier=push` rows of `config/check/must_check_gates.sdn`, calls `plan_integration_with_manifest` (`:67`) and `lifecycle_gate_bundle_admits`, persists one audit record via `lifecycle_store_write`, mutates nothing. | IN — the open half of item 2 | 2 | yes | First reachable PASS: `PASS — 1 operation(s) planned, admitted as dry-run only` (`:180`) with all nine steps (`:54-64`) printed and one record readable back through `devhub lifecycle inspect`; one negative fixture per rejection code `SJ_OBSERVE_ONLY`, `SJ_POLICY_TARGET`, `SJ_IDENTITY_MISSING`, `SJ_REMOTE_STALE`, `SJ_POLICY_MISSING`, `SJ_AUTHORITY_MISSING`, `SJ_GATE_BUNDLE`, `SJ_APPROVAL_STALE`, `SJ_GATE_MANIFEST`, `SJ_POLICY_UNKNOWN`, `SJ_GATE_EVIDENCE_MISSING`; a manifest that selects zero push-blocking gates is ERROR (`gate_manifest.spl:97`). `lifecycle_gate_bundle_admits` goes from 0 to ≥1 `src/` caller. |
| 4 | Reachability guard `scripts/check/check-lifecycle-reachability.shs` (item 5). Another agent is building it now — this row is the contract only. | IN | 3 (else it is honestly RED on `lifecycle_gate_bundle_admits` and `plan_protected_gate_manifest`) | yes | `--selftest` fatal, then `PASS — <n> symbol(s) checked, 0 unreachable` with n > 0; ERROR on 0 symbols scanned; a `push`-tier row in `config/check/must_check_gates.sdn` AND the byte-matching case arm in `check-push-must-pass.shs` (a row alone is not wiring — `.claude/rules/vcs.md`). If it must land before step 3, it lands `push_blocking: false` with the RED symbols named, never with a widened allowlist. |
| 5 | NFR sys-test rows (NFR-001/003/004/005/006/008) and one fault-injection row in `doc/03_plan/sys_test/scv_jj_git_devhub_spipe_unified_lifecycle.md`. | IN | — | yes — **landed 2026-09-05 in this change** | Rows exist with fail-closed oracles; the executable specs that carry them land with steps 3 (NFR-001/003), the store round-trip (NFR-004/fault), and the measurement pass (NFR-005). Rows are plan text, not evidence: a row with no spec behind it is recorded as `no spec yet` in the cross-walk, never as PASS. |
| 6 | Stage 0.5 exit measurement: re-run `legacy_argv_dry_run_plan_spec`, `lifecycle_record_store_spec`, `lifecycle_local_provider_spec`, `gate_manifest_spec`, `integration_policy_evidence_spec`, `lifecycle_policy_plan_spec` once on the seed; record binary identity (`readlink -f bin/simple` + `stat`) beside every number. | IN | 1-5 | yes (diagnostic only) | Cross-walk row 0.5 updated to "AC-5 diag PASS; AC-7 diag PASS; executor + guard landed"; the ceiling paragraph above stays. |
| — | Authoritative PASS for any AC; `$verify STATUS: PASS`; promotion of Stage 0.5. | IN, but **BLOCKED** | non-seed `bin/simple` | **no** | Not closable on this machine. Do not write "verified" anywhere in this lane until `bin/simple --version` no longer prints the seed warning. |

Items that are OUT of "Stage 0.5 done", with where they actually belong:

- **`scripts/check/land.shs` raw push (`:100`) and its "separate reviewed CAS
  operation" message (`:101`).** Replacing the push with a live executor is
  Stage 2 item 4 (live lease/CAS for `integration/main` only, after parity
  against the Stage 0.5 dry-run plans). Routing `land.shs --dry-run` (`:94-97`)
  through the planner is Stage 0 item 4, and because `use` is eager and
  `land.shs` is on the push path, it shells out to `bin/sj plan` rather than
  importing the planner. After step 3 the `:101` message should name
  `sj integrate --dry-run` as the observe-only executor; that one-line
  truthfulness edit is the only `land.shs` change in Stage 0.5's scope.
- **Four of five `LifecycleProvider` traits with zero implementers
  (`lifecycle_provider.spl:13-30`; only `LocalScvProvider` implements
  `LifecycleProvider`, `lifecycle_local.spl:15`).** `ReviewProvider` and
  `ReleaseProvider` get their first implementer in Stage 4 (GitHub);
  `TaskProvider`/`KnowledgeProvider` in Stage 5. Writing four implementers now
  to make the count non-zero is the unused code the repo forbids; the count
  stays 1/5 through Stage 0.5 and is recorded as expected, not as a gap.
- **Stage 6a provider design (GitLab/Gerrit/Review Board/Bitbucket).** Stage 6
  work. Not a Stage 0.5 item and not padding for this list.
- **Stale `doc/06_spec` manuals** (`_spec.md:201,:207`,
  `_acceptance_spec.md:103,:109`). Owned by the `doc/06_spec` lane; an
  authoritative regeneration is blocked on an admitted pure-Simple CLI. A
  seed-run `spipe-docgen` from source would refresh the SHA rows but is itself
  diagnostic, so it does not close the item.

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
| 0.5 | REQ-002, REQ-009 | AC-5, AC-7 | `01_unit/app/sj/legacy_argv_dry_run_plan_spec.spl` (6/6), `01_unit/app/devhub/lifecycle_record_store_spec.spl` (7/7), `01_unit/app/devhub/lifecycle_local_provider_spec.spl` (3/3) | AC-5 wired via `sj plan`; AC-7 has a local write path. Both diagnostic-only — deployed `bin/simple` is the Rust seed. Items 2 (gate-manifest/CAS half) and 5 (reachability guard) still open; policy-parse defect (path step 1) blocks the PASS branch |
| 1 | REQ-001 | AC-1, AC-2 | `01_unit/lib/scv/lifecycle_entity_codec_spec.spl`, `lifecycle_identity_spec.spl`, `lifecycle_codec_spec.spl` | diag; no importer |
| 2 | REQ-003, REQ-002 | AC-3, AC-6 | `01_unit/lib/scv/lifecycle_review_sync_release_spec.spl`, `01_unit/app/sj/integration_policy_evidence_spec.spl`, `gate_manifest_spec.spl`, `03_system/app/scv/feature/..._lifecycle_spec.spl` | diag; no executor |
| 3 | REQ-006 | AC-9, AC-10 | `01_unit/app/devhub/version_manifest_spec.spl`, `lifecycle_review_sync_release_spec.spl` | diag; T-1..T-4 open, no arch |
| 4 | REQ-004, REQ-005 | AC-7, AC-8 | `lifecycle_command_spec.spl`, `lifecycle_review_sync_release_spec.spl` | diag; 0 provider impls |
| 5 | REQ-007 | AC-11 | `01_unit/lib/scv/lifecycle_work_spec.spl` | diag; no sync |
| 6a/6 | REQ-004, REQ-008, REQ-009 | AC-15, AC-17 | none | absent; no design |
| 7 | REQ-010, NFR-007 | AC-18 | none | blocked |
| all | — | AC-12, AC-13, AC-14, AC-16 | `03_system/app/scv/feature/..._acceptance_spec.spl` (trace inventory), stale manuals | AC-13/18 blocked on admitted CLI |

Sys-test plan rows (`doc/03_plan/sys_test/scv_jj_git_devhub_spipe_unified_lifecycle.md`)
cover REQ-001..010 + NFR-002/007 in the first table; the second table (added
2026-09-05) carries NFR-001/003/004/005/006/008 and one fault-injection row
(research 1 §18.7). Rows are plan text; each names the spec that will carry it
and its owner stage, and none is evidence until that spec runs.

## NFR ownership (sys-test rows added 2026-09-05; executable specs pending)

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
- 2026-09-05 (later): Stage 0.5 items 1, 3, 4 landed (`35a216c1923`,
  `e6446521cd3`). Found the committed `.spipe/policy/vcs.sdn` rejected by
  `parse_lifecycle_vcs_policy` (indent-blind scan); "Path to Stage 0.5 done"
  sequenced; NFR/fault-injection sys-test rows added.

## Next change

Stage 0.5 only, in the order of § "Path to Stage 0.5 done": fix the policy
parser (step 1), wire `sj plan` to the policy (2), add the dry-run executor (3)
and reachability guard (4), then re-run the focused specs once on the seed and
record binary identity (6). Do not combine wiring, evidence recovery,
public-ref mutation, or release publication in one change. Nothing in this
lane may be called "verified" until a non-seed `bin/simple` is deployed.
