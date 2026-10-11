# Feature: simple_traceability_sdn_slop

## Raw Request

Re-research the saved traceability report with Astra through `$sp_dev`, plan and
design the full feature, enumerate modern SSpec acceptance tests, implement in
parallel, land on the release branch, and make this development fully traceable.

## Task Type

feature

## Refined Goal

Implement the complete SDN-only shared trace graph, exact-snapshot admission,
runner-owned eligible evidence, deterministic documentation, static publication,
and native Slop viewer described in the 2026-10-03 report, with the feature's own
requirements, scenarios, source, execution evidence, and delivery linked.

## Baseline and ownership

- Report: `doc/09_report/simple_traceability_sdn_slop_final_2026-10-03.md`.
- Original implementation baseline: `88ecaa21054aea80eb7c8dd46052c344837fe78a`.
- Release integration baseline: `20f619fe31baa4decbe40f6d367fb5e4f115bbd8`.
- Branch: `work/traceability-release_phase3-20261011`.
- Workspace: `C:/dev/simple-traceability-phase2-release-20261011`.
- Merge owner: root. Final architecture/evidence reviewer: Astra.
- No other session's changes belong to this lane.
- User-confirmed release destination: `release_phase3`.
- User explicitly confirmed the full report scope and NFR targets.
- User now requests Phase 3 build/run validation before release PR landing.
  Phase 2 verification is historical. Record compiler and
  runtime-provider identities; do not substitute seed execution for this lane.

## Recovery checkpoint

Current Phase 3 checkpoint: see `phase3_verification.md`. The branch was rebased
onto the fetched release revision with recovered untracked feature files retained.
No implementation commit, feature verification PASS or release merge is claimed.

The original uncommitted worktree was absent. Source and intent were reconstructed
from its parent and three child session transcripts, using literal patches and
recorded data only. The original source was not executed during recovery. Existing
runner modifications are being integrated against the current release rather than
overwriting it with the old baseline. This checkpoint is neither implementation
completion nor verification evidence.

Phase 2 compiler: `C:/dev/simple-bootstrap-storage/rel-s2rebuild/frozen/simple.exe`.
SHA-256: `b0e786b3c74c9c2e8bb125967829cdb083d21480c526739d254ff6b5390c566c`.
The frozen capsule receipt binds the same compiler and native runtime archive.
The focused host probe reached native compilation; link qualification is pending.
The worktree uses isolated caches and a pinned LLVM toolchain. No acceptance
criterion has passed and no feature implementation PR has merged.

## Acceptance Criteria

1. Preserve and prove every REQ-TRC-001 through REQ-TRC-020 and every
   AC-TRC-001 through AC-TRC-040; the detailed test plan maps independent oracles.
2. Re-research local owners and external primary sources with Astra; retain
   discrepancies, source revision, and evidence rather than treating the report
   as current implementation proof.
3. Produce requirement, NFR, architecture, detail/UI design, full acceptance
   plan, executable modern SSpec and readable mirrored manuals.
4. Implement the report's full shared-graph behavior, SDN boundaries, exact
   candidate gates, evidence, projections, native viewer and extension seams.
5. Link this feature's own requirements, test definitions, implementation,
   actual runs, unresolved work, review and merged delivery. Never call planned
   scenarios executed or unverified results PASS.
6. Integrate through a reviewed release-targeted PR under release policy; no
   tags or external artifact publication are authorized by branch landing alone.
7. Update affected research/design/plans, developer guides, feature and layer
   expert knowledge, generated manuals, and workflow skill/agent/command
   instructions. Record every unfixed gap with owner, location and unblock
   condition; unavailable host rows remain active, not excluded.
8. Verify exact source-matched pure-Simple runtime, production integration,
   negative cases, incremental/full equivalence, actual native UI and supported
   host performance before claiming full completion.

## Cooperative Review

- Astra: local/domain re-research and final architecture review.
- Acceptance lane: complete modern SSpec matrix and runner/evidence inventory.
- Viewer lane: native UI/source/projection design and API inventory.
- Root: integration, requirements, shared model, contracts and delivery.
- Lower-model sidecars: N/A; selected lanes require semantic/authority review.
- Shared API and helper contracts freeze in detail design before source work.
- Missing acceptance fixtures fail explicitly (`fail(...)`), never placeholder
   pass, skip, source-string inventory, or an observation compared to itself.
- Section/directory test execution is serialized through root.

## Phase

paused-awaiting-runtime (user-requested wait; implementation incomplete)

## Log

- 2026-10-03: report was saved unchanged and merged as PR #2315.
- 2026-10-03: isolated existing session workspace reused on a new work branch;
  baseline refreshed to the merged report. Three parallel research/design lanes
  started; Astra explicitly selected by the user.
- Context-mode MCP tools are unavailable in this session. Bounded shell output
  is used; no direct HTTP shell fetching or raw large output is required.
- Shared SPipe home routes absent; initializing the pinned `.spipe/spipe`
  compatibility submodule rather than inventing replacement guidance.
- No admitted Stage 4 binary identified yet. `C:/dev/simple/bin/simple.exe`
  exists but its age/name alone is not provenance or permission to use a seed.
- Astra local/domain re-research complete; all 40 original acceptance criteria
  and seven development/self-traceability scenarios enumerated. Three parallel
  source lanes now own kernel, evidence and viewer; root owns integration.
- Pinned common resolved by the shared locator using Node's installed absolute
  path: `.spipe/spipe` at `0a00354eeea87ab7a74ef6e1aa3b8d5756bc1b75`.
- Source work now includes exact push-ref and byte-framed Git-object decoders,
  dependency invalidation planning, immutable registered-declaration extraction,
  shared graph/evidence contracts and native Slop. These are authored, not
  compiled or executed. Full adapter, performance and security acceptance is
  still open.
- User confirmed scope/targets and release/1.0, and asked to wait for runtime
  readiness. Runtime verification and landing are held accordingly.
- Parallel source lanes reached a retained checkpoint. Kernel has 29 authored
  focused cases; evidence has 12 authored cases; viewer and snapshot/invalidation
  cases are also authored. All are in-development and NOT RUN. These counts are
  inventories, not execution or coverage evidence.
- Source review corrected duplicate canonical file identities in snapshot
  extraction, test-kind qualification facets, native focus/source state, and
  diagnostic event framing. Remaining work is retained in `resume.md` and the
  full acceptance plan; no implementation PR or release merge exists.

## Completion evidence

None yet. Research and authored plans are not executed acceptance evidence.

## Latest steering

User requested landing on the release branch, then `/compact prepare
verification to phase 4 runtime`. See `phase4_verification.md` for the compact
runtime admission and exact focused-test handoff. Release landing remains
authorized and pending; no implementation or test completion is claimed.

2026-10-04 continuation: verified the retained branch and dirty checkpoint;
both expected release-runtime directories are still absent. Added explicit
plan/event/finalization reload and interruption checks to the Phase 4 handoff
after inspecting the real persistence methods. Runtime verification remains
NOT RUN. No bootstrap restart, implementation PR, or release merge occurred.

2026-10-04 release reconciliation: fetched `origin/release/1.0` at
`f5fec9ccf8c`. Its tree contains neither `src/lib/common/traceability` nor
`src/app/slop` nor this feature's architecture document. The merged-PR search
for traceability on that base returned no results. Therefore this feature is
not established as landed; unrelated release PRs do not discharge its goal.
The local lane still has uncommitted work. Added an in-development integration
spec at `test/02_integration/app/traceability/snapshot_graph_spec.spl`, covering
production extraction/resolution/SDN/query composition, quoted-ID rejection
and missing-target diagnostics. It is NOT RUN and not a CLI/system acceptance.

2026-10-04 static publication source: added `common/traceability/html.spl` and
four in-development unit scenarios. The shared graph projects into deterministic
offline HTML with escaped metadata, inert navigation, explicit visible-node
selection and hidden counts. No JSON/JavaScript, source export, or unearned run
badge is emitted. Publication authorization/transactions, evidence/provenance
views and actual browser acceptance remain open. These new specs are NOT RUN.

2026-10-04 self-traceability: authored the initial `simple.trace.declarations/v1`
file under `doc/08_tracking/trace/features/simple_traceability_sdn_slop.sdn`.
It records all 20 selected requirements and explicit document/kernel/suite
relationships. Referenced paths were checked for existence, which is not SDN
parse or execution evidence. Registration/authority, case metadata, full source
coverage, actual observations and delivery provenance remain open.

2026-10-04 evaluator review: fixed obligation identity validation before
coverage aggregation. All entries sharing a duplicate ID are incomplete,
including a not-applicable entry; an empty-ID exemption is also rejected.
Added three in-development regression scenarios for duplicate required entries,
both required/exempt orderings, and empty-ID exemption. These are authored
regressions from a source-level finding, NOT RUN against an admitted runtime.

## 2026-10-11 scoped continuation on release_phase3

Draft PR #3083 retains commits through cabd1dd91f4. The full goal is active;
the previous resource audit changed the prerequisite evidence but did not
qualify or land any feature. All 40 system criteria remain not_run.

Astra re-reviewed the current source and appended research/design corrections:
selected scope needs a retained contract; previous persist_trace_plan/final API
claims were inaccurate; runner persistence actually followed docgen; the pure
invalidation planner is not a persistent incremental graph store. Those older
claims do not establish implementation.

Current source adds scope-bound graph composition and an exact-snapshot local
preview route, a pure frozen-plan/event reconciler, and missing/partial/cached
runner-transport rejection. Results persist before docgen. Astra found and root
fixed a content-identity collision, unsupported empty scope roots and empty
feature plans. New regression scenarios are authored, not executed.

The self-trace declaration described in the old checkpoint was absent from the
recovered release branch. It is now explicitly authored with all 20 requirements
and 40 planned criteria and current artifact links. Native parsing, case-level
SSpec bindings and declaration authority are still pending; no history or PASS
was reconstructed. Stage 3 build qualification and the full runner/manual
runtime remain absent. Storage cleanup found no safely disposable large cache;
active build and recovery data were preserved.
