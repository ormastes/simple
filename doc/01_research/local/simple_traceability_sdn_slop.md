# Traceability, SDN, and Slop: local re-research

<!-- codex-research: Astra, 2026-10-03 -->

## Audit boundary

This is source research, not execution evidence or a completion claim. The research baseline is `88ecaa21054aea80eb7c8dd46052c344837fe78a` on `work/traceability-sdn-slop-20261003`. The [source report](../../09_report/simple_traceability_sdn_slop_final_2026-10-03.md) audited an older revision, `02f6687d846ba55faea4a08c44e4a3c0982a488d`. Its REQ-TRC-001–020, AC-TRC-001–040, WP0–WP7 and published NFR targets remain the complete scope selected by the user's instruction to implement the report, as confirmed by parent coordination. This research does not remove obligations or auto-select a reduced alternative.

The assigned worktree was clean at the opening status check. This lane owns only this document and its [domain companion](../domain/simple_traceability_sdn_slop.md). Parent coordination owns requirement selection, routing records, implementation allocation, and landing. No source edits, binary checks, benchmark runs, ruleset API reads, or feature acceptance runs were performed in this research lane. Other agents' concurrent edits are outside this baseline audit.

Context-mode tools were absent from the available tool inventory. Research used bounded local reads and primary-source web search without direct URL fetching. The common SPipe route was initially unavailable; parent subsequently initialized the existing compatibility pin `.spipe/spipe` at `0a00354eeea87ab7a74ef6e1aa3b8d5756bc1b75`. Read guidance comprises its skills/wiki indexes, canonical research skill, ownership/setup and scope-resolution documents. Parent verified that `scripts/find-spipe.mjs --agent-guide` resolves this pinned compatibility route. Only common and this authorized project were consulted; private company, organization, user and host scopes were not inferred from filesystem presence.

At the audited revision, `doc/00_llm_process/knowledge_registry.sdn` has no exact feature route for `simple_traceability_sdn_slop`. Longest-prefix selection is `src/app` → `app_editor_tooling`, and `src/lib` → `runtime_memory_io`, both `mdsoc_plus`. Their layer instructions place CLI composition in apps and runtime/environment/process effects behind owning facades. Parent is adding the exact feature route and selection receipt; absence of that route is an identified setup gap, not implicit permission to invent existing expertise.

## Verified current ownership

| Owner and inspected source | Current fact | Consequence |
|---|---|---|
| `src/app/traceability/core.spl` | Reexports `_TraceabilityCore/config_and_analysis`, `warning_counts`, and `manifest_and_report` | Keep the command façade while moving genuinely shared pure semantics to a library. |
| `_TraceabilityCore/config_and_analysis.spl:103–121` | `analyze_repo_traceability` collects files and delegates to `analyze_virtual_files` | `VirtualFile(path, content)` is a useful adapter seam; filesystem enumeration need not enter the new semantic kernel. |
| Same file, `195–275` | Collector accepts source/test `.spl` and documentation `.md`; parsed requirements are extracted by text prefix | Tracking SDN is absent from this collector. Substring occurrences cannot establish scenario-level acceptance edges. |
| `config/traceability.sdn` | Source warning roots remain commented out | Existing enforcement is opt-in; do not claim repository-wide source coverage. |
| `src/app/tracking/main.spl:100–125` | Done-row checks read numeric columns and test selected fields for blank values | Replace qualification with schema-aware named fields and shared graph obligations; retain feature lifecycle intent as independently authored state. |
| `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl:26–111` | `RunnerTestDb` wraps `TestDatabaseExtended`, owns run IDs, result updates, completion, and resource records | Extend this boundary; do not create an independent graph-owned mutable results database. |
| `src/app/spipe_docgen/spipe_docgen/evidence_loader.spl:158–192` | Splits legacy sidecars on `---`, parses custom key/value records, then renders blocks without manifest admission | Provide an explicit versioned importer; a `.sdn` suffix does not make legacy bytes valid SDN or trusted evidence. |
| `src/lib/common/spec/evidence/model.spl:499–581` | `EvidenceManifest` carries provider/run/spec/artifact identities; completeness checks digest shape | Reuse available types, but digest shape is not artifact-byte verification, build-input equivalence, or producer authentication. |
| `scripts/hooks/pre-commit:68–85` | Runs broad tracking generation, strict DB checks, and full-scope traceability, with legacy structured log flags | Move maintenance generation out of minimum trace validation while preserving unrelated existing guards. |
| `scripts/check/pre-push-conflict-tree-guard.shs` | Captures ref rows before child tools and rejects capture failure/empty input; delegates existing checks and receipt handling | Extend this canonical boundary and its must-check driver; a second competing launcher risks missed refs and recursion. |
| `.github/workflows/required-gates.yml:73–142` | Missing PR range exits successfully; BASE pins the manifest, but comments acknowledge executing candidate gate code | Resolve every supported event's subject and isolate trusted checker code, imports, configuration, and control plane. A manifest-only pin does not close the gap. |

These observations reconfirm the report's material baseline findings. Repository settings remain separately mutable: the report's required-context names are historical input until verified against the actual landing branch's current rules. No settings inspection occurred here.

## SDN correction that affects implementation

Use `std.common.sdn.value.SdnValue`, `std.common.sdn.parser`, `std.common.sdn.schema`, and `std.common.sdn.encode.sdn_encode_canonical`. Do not use `std.sdn.render_value`: the shim at `src/lib/sdn/__init__.spl` renders `Table` as `[]` and concatenates strings without the canonical encoder's escaping.

`common/sdn/encode.spl` explicitly limits its table round-trip guarantee to top-level tables. It documents unsupported nested tables in inline dictionaries/arrays, problematic structural characters in keys/headers, and floating exponent caveats. The report's multiple named tables are therefore a proposed document shape that needs codec evidence, not an established serialization guarantee. A viable initial representation is a schema-versioned dictionary containing arrays of dictionaries with restricted schema keys and integer-only counters/durations. This remains ordinary SDN, preserves normalized records, and avoids a private parser or JSON fallback. Final choice belongs to design after executable codec fixtures.

`parse_with_issues` exposes duplicate-key issues; default `parse` alone is insufficient for rejection policy. `parse_untrusted` adds a 1 MiB input bound, depth 64 and collection limit 65,536, but calls `parse`, so those limits do not automatically reject duplicate keys. Combine bounded parsing and issue/schema validation deliberately. The report's ordinary hook workload permits up to 2 MiB across relevant inputs: limit individual documents or define a measured configured decoder bound; do not silently discard oversized graph records. `schema.spl` distinguishes optional absence from type mismatch and required fields, and warns about value-copy mutation hazards. Add explicit tests for empty versus absent values, integer extrema/overflow, duplicate table headers, malformed quotation, unknown major version, invalid enum, endpoint closure and escaping.

## Proposed interface freeze for parent design

These are proposed interface contracts, not existing APIs. Keep immutable record definitions and semantic functions under `src/lib/common/traceability/`. Use closed enums for states and validated identifier fields. Representation and field names must be frozen once by the merge owner before workers implement them.

| Record | Required contract |
|---|---|
| `SnapshotSubject` | Repository identity, snapshot kind, object format, exact tree/commit or frozen input identity; worktree preview is distinguishable. |
| `SnapshotArtifact` | Repository-relative path, blob identity, bytes/content, visibility, extraction mode; no arbitrary filesystem locator. |
| `SnapshotInput` | Subject, artifacts, complete inventory identity, explicit completeness state. |
| `TraceNode` | Stable ID, typed kind, title; identity is separate from current file path and presentation occurrence. |
| `TraceClaim` | ID, endpoints, relation, origin ID, operation, named rule/scope; declarations are separate from resolved edges. |
| `TraceEdge` / `TraceOrigin` | Canonical endpoints/relation versus attributable declaration/rule/version/location. |
| `TraceLocator` | Entity, pinned subject, repository-relative path, locator kind/range, visibility. |
| `TraceDiagnostic` | Code, subject, rule, entity, origin, message, severity; infrastructure failure is representable. |
| `TraceGraph` | Subject/input manifest/generation, normalized nodes/claims/edges/origins/locators, diagnostics, completeness. |
| `TraceObligation` | Requirement/criterion, verification kind/config/lane, applicability and all/any satisfaction rule. |
| `TraceRun` | Planned cases, definition/source/config/expectation/binary identities, retained attempts, observations/artifacts, terminal/missing-shard state. |
| `AdmissionContext` | Independently established producer/artifact/input verification facts; never trust a candidate's self-declared verified boolean. |
| `TraceQualification` | Obligation outcomes, eligible evidence, refusal reasons, structural and verified numerators/denominators. |

Proposed pure functions, in Simple type notation:

- `decode_trace_document(source: text) -> Result<TraceDocument, [TraceDiagnostic]>`
- `encode_trace_document(document: TraceDocument) -> Result<text, [TraceDiagnostic]>`
- `extract_trace_facts(input: SnapshotInput, policy: TracePolicy) -> TraceFacts`
- `resolve_trace_graph(facts: TraceFacts, policy: TracePolicy) -> TraceGraph`
- `update_trace_graph(index: TraceIndex, delta: SnapshotDelta, policy: TracePolicy) -> TraceUpdate`
- `evaluate_obligations(graph: TraceGraph, obligations: [TraceObligation], run: TraceRun, admission: AdmissionContext) -> TraceQualification`
- `project_trace_markdown(graph: TraceGraph, qualification: TraceQualification) -> [TraceOutput]`
- `query_trace_graph(graph: TraceGraph, query: TraceQuery) -> TraceQueryResult`

Effectful snapshot adapters, clocks, environment/process access, object reads, durable writes and admission provenance checks stay outside these functions. Runner integration calls the existing outcome writer, then supplies immutable records to the evaluator. Docgen remains the manual renderer where applicable; Slop consumes projected models, never re-extracts repository semantics.

## Design invariants and verification gaps

1. **Exact subject:** index inventory and staged bytes, revision trees, SJ frozen candidates and worktree previews are separate adapter products. Preserve alternate index, linked-worktree and unusual-path handling. Captured push rows cover every ref, deletion, creation, tag and non-fast-forward policy case. Changed files select work; they do not define the full endpoint universe.
2. **Semantic honesty:** conventional source/unit paths establish structural associations only. Explicit owned SSpec/SDN declarations establish requirement/criterion claims. Quoted examples, generated manuals, linked tests and completed feature rows cannot grant verified execution.
3. **Dependency completeness:** cache blob/extractor/rule/schema identities and positive, absent, unique-ID and membership dependencies. Duplicates, deletion, aliases and unchanged incoming references require invalidation. Incremental/full equality requires independent rebuild fixtures, including randomized edits. Display limits must not affect qualification.
4. **Execution provenance:** separate outcome, evidence validity, applicability and qualification. A real acceptance-only run leaves linked lower-level tests not run. Crash/cancellation/missing shard/zero discovered versus planned cases remain incomplete. Retain attempts and expected-failure distinctions. Reuse requires validated input closure, lane and actual binary/build relation.
5. **Publication:** structural manifests exclude their own generated outputs; run receipts bind the complete candidate externally. Deterministic stable documents and immutable run reports are different products. Imported legacy evidence remains unverified where provenance is missing. Migration must demonstrate interrupted/concurrent updates without duplicate writers or lost links.
6. **Viewer and export:** canonical nodes may occur in multiple MDSOC branches without identity duplication. Preserve revision-pinned source, explicit last-valid state, resync after lost/mismatched delta, keyboard focus and relationship-list alternatives. Public export needs visibility filtering and context-correct escaping; UI truncation exposes hidden counts.
7. **Deployment and performance:** source inspection does not establish a source-matched self-hosted binary, Git/jj/SJ route behavior, trusted remote producer, supported-host latency, or RSS. Preserve all report targets as unmeasured until recorded against identified binaries/fixtures/hosts. No test-suite sweep belongs inside a normal hook.

## Full-scope work-package handoff

WP0 must pin executable/settings/host baselines and establish the trusted execution route. WP1 freezes and verifies the shared codec/model. WP2 owns extraction/resolution. WP3 owns incremental snapshots and local/remote admission. WP4 owns runner integration and evidence migration through the existing writer. WP5 owns deterministic Markdown and safe offline HTML. WP6 owns the native three-pane Slop surface. WP7 retains architecture/design/dependency views and the admitted future distributed-adapter seams; it is not silently removed because a minimal graph slice works.

The feature itself is the first fully linked slice: all 20 requirements and 40 acceptance scenarios need explicit authored associations, executable test owners, actual observed run status and generated navigation. In-memory unit fixtures are necessary but insufficient: at least one feature SSpec must drive extraction, resolution, runner, reports and source navigation through production boundaries. Acceptance entries remain planned/unexecuted until those tests run. Parent owns the complete acceptance ledger and any requirement/NFR decision.

The current typed-evidence design at `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md` is a relevant prior authority: ordinary `describe`/`it`/`step`/`expect`, positive production oracles, fail-closed selectors and docgen-owned rendering. Its as-built deviations must be read alongside source. `doc/05_design/simple_distributed_textual_databases.md` remains a design direction: preserve SCV identity and SJ mutation ownership without claiming its distributed reducer/settlement is deployed or blocking the local feature on it.

## Research status

Source audit and primary-source re-research complete. Implementation verification: **NOT RUN**. Performance: **NOT MEASURED**. Remote settings/admission: **NOT VERIFIED**. Requirements and NFR selection: full saved report, selected by the user's implementation instruction and retained by parent coordination. No readiness PASS is asserted.

## Phase 3 corrective source review — 2026-10-11

<!-- codex-research: source-contract correction, 2026-10-11 -->

Reviewed HEAD `cabd1dd91f42ecd6e0a5daa2abac8937aebb03e2` in the isolated
`work/traceability-release_phase3-20261011` lane. This appendix supersedes
as-built assertions above where the recovered Phase 3 source differs. It
does not replace the selected 20 requirements, 40 acceptance criteria or NFRs.
No executable, tests, remote settings or external research were invoked: the
existing domain research answers the design questions; the defects here are
observable local integration gaps. The current runtime prerequisite is the
user-requested admitted, source-matched **Phase 3** compiler, not an automatic
upgrade to the older document's Stage 4 target.

The retained knowledge receipt names layer guides absent from this checkout.
The `.spipe/spipe` directory exists but its `wiki/index.md` is absent. These
are stale/unavailable guidance inputs to repair through the merge owner, not
evidence that common guidance was consumed at this revision. Canonical research
and design skills were read from `C:/dev/simple/.codex/skills`; their worktree
copies and context-mode tools were unavailable. Only assigned documents are
edited by this review lane.

### Four blocking contract gaps, in implementation order

1. **Snapshot identity is pinned; scope and graph assembly are not yet bound.**
   `snapshot/git_provider.spl::snapshot_git_inputs` verifies Git blob bytes and
   freezes index/commit trees, but marks `complete` relative to the caller's
   selected paths. `SnapshotInput` does not retain those roots or a closure
   receipt. `extract/snapshot_facts.spl::extract_snapshot_trace_facts` accepts
   externally supplied manifest/generation strings. `main.spl` still invokes
   `analyze_repo_traceability`, the worktree warning collector, rather than the
   snapshot/extractor/resolver pipeline. Bind selected scope and exact policy
   records into a canonical structural manifest, bind subject into generation,
   and expose selected-scope preview honestly. Trusted admission requires its
   separate policy-closure check (AC-010–020,029–030); a hash alone is not that
   check.
2. **Authored graph declarations do not establish executable scenario identity.**
   The extractor accepts registered SDN declarations and file inventory only;
   it explicitly rejects every non-file locator as requiring an admitted
   symbol/section extractor. It neither parses scenario `@req` metadata nor
   proves a declared case corresponds to an actual discovered SSpec case.
   `TraceCaseEvent` carries only `case_name`, `phase`, `outcome`, so duplicate
   display names, parameter instances, retries and shards cannot be mapped
   unambiguously without a pre-dispatch binding. Freeze a case plan and reject
   ambiguous event mapping; do not use declaration presence as execution proof
   (AC-007,021–025 and self-traceability).
3. **The recovered runner lacks the transaction described by the old checkpoint.**
   `RunnerTestDb.record_trace_case_events` exists; `persist_trace_plan` and
   `persist_trace_final` do not exist in the reviewed runner/database sources.
   `update_test_database_from_record` starts and completes a run after execution.
   The live app delegates persistence to `test_db_lane_main.spl` to keep database
   modules out of the runner's static closure. Its docgen call precedes that
   delegation and returns early on failure; the delegation itself returns void
   and prints warnings for failed writes/child exit. Preserve the existing
   child-owner boundary, persist observations before rendering and propagate
   infrastructure failure. Then add durable plan/final/recovery transactions;
   ordering alone does not solve crash, zero-discovery or migration safety
   (AC-021–022,027).
4. **Invalidation planning is not an incremental graph store.**
   `incremental.spl::plan_trace_invalidation` is a bounded dependency-closure
   planner. There is no implemented `TraceIndex`/`SnapshotDelta`/`TraceUpdate`
   workflow in that module, and extraction does not emit its dependency records.
   Retain full rebuild as the authority until file-fact ownership, dependency
   capture, removal/replacement and atomic generation publication are connected.
   Planner unit cases alone cannot establish full/incremental equivalence or
   performance budgets (AC-005,008–009,028,038).

The shared resolver, codecs, query and evidence records are useful existing
building blocks. They do not close the independent trusted remote gate,
visibility/source owner, native viewer, recovery or host qualification work.
Parallel implementations after this HEAD must receive exact-diff source review;
this appendix is not their execution receipt. Review status: **SOURCE GAPS
IDENTIFIED; IMPLEMENTATION INCOMPLETE; EXECUTION NOT RUN**.
# 2026-10-11 Git-object guidance correction

The sparse-worktree observation of absent layer guidance does not establish
absence from this source revision. `git show HEAD:` successfully read both
`doc/00_llm_process/layer_base/app_editor_tooling/skill.md` and
`doc/00_llm_process/layer_base/runtime_memory_io/skill.md`. The registered
longest-prefix routes therefore resolve in the Git tree and their owning-layer
guidance was read. `.spipe/spipe` is a pinned gitlink at
`0a00354eeea87ab7a74ef6e1aa3b8d5756bc1b75`; an uninitialized local directory does
not prove that `wiki/index.md` is absent from that submodule revision. Common
wiki materialization and provenance inspection remain separate prerequisites.
