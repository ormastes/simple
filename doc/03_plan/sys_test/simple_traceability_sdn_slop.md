# Simple traceability SDN, gates, evidence, and Slop acceptance plan

Status: PLANNED / NOT EXECUTED. This inventory is not a qualification receipt.
Source: `doc/09_report/simple_traceability_sdn_slop_final_2026-10-03.md`, sections 4, 13, 19, and 22.
Owner: traceability feature merge owner; final review: independent parent/reviewer. Prepared 2026-10-03.

## Scope and evidence contract

All 40 report acceptance criteria are mandatory within their applicable capabilities. Requirement numbers below expand to `REQ-TRC-NNN`; they are explicit scenario associations, never substring-derived coverage. One criterion may need multiple scenarios and test layers. Every executable scenario must carry its exact `@req` associations and criterion identity, a user-voice purpose/workflow/limitations docstring, outcome-named `it`, imperative `step`, and real captured output. `@manual_section` groups operator workflows. Generated manuals contain observations only when a receipt establishes execution; planned narrative must never say screens were captured or checks passed.

Manuals mirror executable paths after stripping `test/` and replacing `.spl` with `.md`, under `doc/06_spec/`. Never put executable specs there. Existing `test/03_system/plan_acceptance/evidence_showcase_spec.spl` demonstrates manual metadata but includes source-count oracles and known missing imports: it is not a model of runtime qualification. The scenario-manual guide's example is illustrative, not evidence for this feature.

## Frozen proposed helper vocabulary

These names describe acceptance adapters, not existing production APIs. Parent confirms interfaces before executable authoring.

- `trc_fixture_create(case_id)`: isolated repository and artifact root, independently specified expected identities.
- `trc_invoke_candidate(fixture, profile)`: compiled production CLI invocation with candidate identity, stdout, stderr, exit, elapsed/resource observation. No source-text verdict inference.
- `trc_read_run_artifacts(run_id)`: actual persisted SDN and Markdown plus verified digests, not reconstructed expected output.
- `trc_assert_subject(result, expected_subject)`: compare independently obtained staged tree/frozen candidate/revision against receipt.
- `trc_assert_obligation(result, obligation_id, expected_state)`: typed obligation, execution and validity assertions; linked is not executed.
- `trc_capture_result(label, result)`: retained real command/receipt evidence; redact secrets and local absolute paths.

Shared steps: Prepare the isolated candidate; Declare the requirement and acceptance obligation; Run the production traceability command; Inspect the retained SDN result and Markdown report; Verify the exact subject and obligation state. Missing adapters must use `fail(...)` or `assert(false)` with a precise reason. No constant success, skipped mandatory case, source-presence assertion, default empty result, or fixture that manufactures a production receipt. Deliberate-red and zero-executed calibration precede trusting a runner lane.

## Planned test and manual families

Paths below are proposed authoring destinations, not claims that tests exist. Pure/integration files supplement system acceptance, never replace it.

| Key | Executable path | Mirrored manual |
|---|---|---|
| C | `test/03_system/app/traceability/feature/sdn_graph_spec.spl` | `doc/06_spec/03_system/app/traceability/feature/sdn_graph_spec.md` |
| G | `test/03_system/app/traceability/feature/admission_spec.spl` | `doc/06_spec/03_system/app/traceability/feature/admission_spec.md` |
| E | `test/03_system/app/traceability/feature/run_evidence_spec.spl` | `doc/06_spec/03_system/app/traceability/feature/run_evidence_spec.md` |
| V | `test/03_system/app/traceability/feature/slop_publication_spec.spl` | `doc/06_spec/03_system/app/traceability/feature/slop_publication_spec.md` |
| P | `test/05_perf/app/traceability/traceability_budget_spec.spl` | `doc/06_spec/05_perf/app/traceability/traceability_budget_spec.md` |
| S | `test/03_system/app/traceability/feature/self_traceability_spec.spl` | `doc/06_spec/03_system/app/traceability/feature/self_traceability_spec.md` |

Host keys: ALL = native Windows, Linux, macOS; GIT = all three with real Git; JJ = explicitly supported jj version/transport rows; REMOTE = trusted CI candidate matrix; UI = each admitted Slop rendering/input backend on each supported host. Unsupported/absent lanes remain NOT RUN or BLOCKED with an owner, prerequisite, exact resume command, and retained artifact path.

## Full acceptance inventory

Every row initially has evidence state NOT RUN. Fixture/oracle is additional detail, not a weaker replacement for the report criterion. Family identifies both executable and manual above.

| AC-TRC | REQ-TRC suffixes | Family / hosts | Fixture and real oracle |
|---|---|---|---|
| 001 | 001,018 | C / ALL | SDN strings with comma/quotes/Unicode, row order, empty versus absent, signed limits; parse/encode/parse preserves typed values and canonical bytes. |
| 002 | 001,007 | C / ALL | Unknown schema, repeated column, invalid enum, legacy structured-format CLI flags; each fails with explicit schema/rule/entity/subject diagnostic and non-success exit. |
| 003 | 004 | C / ALL | Add source and conventional unit file to isolated tree; real extractor/resolver creates exactly one edge; authored DB bytes remain unchanged. |
| 004 | 005,016 | C / ALL | One shared test and two explicit implementation targets; graph has one test identity and both attributable edges. |
| 005 | 006,017 | C / ALL | Warm unique convention cache then add second candidate; ambiguity diagnostic replaces unique mapping and agrees with cold rebuild. |
| 006 | 005,006,019 | C / ALL | Two rules/scopes and one replacement; only selected edge changes; absent/stale replacement target fails with origin. |
| 007 | 002,013 | C / ALL | Requirement ID in quoted prose plus genuine scenario annotation; only semantic annotation produces accepted-by; prose does not improve coverage. |
| 008 | 007,017 | C / ALL | Cache absent declaration then add it; invalidation clears only affected missing diagnostic and retains unrelated errors. |
| 009 | 006,017 | C / ALL | Duplicate, delete, and cross-directory move target while incoming source is unchanged; all affected references re-resolve and match full rebuild. |
| 010 | 008 | G / GIT | Stage broken/worktree fixed then inverse; result follows independently materialized Git index tree, not workspace bytes. |
| 011 | 008,009 | G / GIT | Alternate index, linked worktree, spaced/Unicode names, case collisions; exact subject/digest confirmed, host collision impossibility recorded explicitly. |
| 012 | 009 | G / GIT | Pipe multiple ref update rows, one invalid; whole push fails, every row is evaluated, child stdin cannot consume remaining rows. |
| 013 | 009,011 | G / GIT+REMOTE | New ref, deletion, forced update, protected tag; explicit result per ref and applicable policy, including empty old/new object IDs. |
| 014 | 008,009 | G / GIT+JJ | Real Git hooks, each supported jj transport, SJ frozen publish; retained invocation receipts prove same evaluator and independently known candidate. |
| 015 | 010 | G / ALL | Remove binary/cache, force timeout/object-read failure/unknown schema; infrastructure or incomplete outcome, never clean; tracked bytes unchanged. |
| 016 | 010,011 | G / GIT | Exercise optimized and generic pre-push dispatch with invalid candidate; both demonstrably call mandatory evaluator and reject. |
| 017 | 011 | G / REMOTE | Candidate changes its runner/gate into no-op; checker/policy loaded from trusted identity still rejects candidate defect. |
| 018 | 011,019 | G / REMOTE | Candidate weakens exclusions/baseline/manifest; unapproved policy rejected; approved independently authorized baseline remains scoped. |
| 019 | 010,011 | G / REMOTE | Documentation/unrelated change; required job executes and emits exact-subject complete scoped result instead of skipped success. |
| 020 | 011 | G / REMOTE | PR head, synthetic merge, merge-group, post-main events; wrong SHA receipt rejected; each event validates its integration subject. |
| 021 | 012,013 | E / ALL | Real feature with acceptance/unit/IT/component obligations, run acceptance only; persisted SDN and Markdown show acceptance execution and three lower layers not run. |
| 022 | 012,013 | E / ALL | Planned cases but zero discovery, absent shard, cancellation, hard crash; terminal/recovered records remain incomplete and keep partial observations. |
| 023 | 013,018 | E / ALL | Mutate source/test/config/expected result/binary-lane individually; stale receipt rejected with reason; unchanged eligible closure reuses receipt transparently. |
| 024 | 011,013 | E / ALL+REMOTE | Forged PASS, plausible digest, absent/tampered artifact, missing producer trust; provenance/artifact verifier rejects each. |
| 025 | 013 | E / ALL | Fail then retry pass, expected fail, unexpected pass; attempts retained separately and qualification uses explicit policy without erasing failure. |
| 026 | 001,018 | E / ALL | Legacy evidence with incomplete provenance imported; history and links preserved, no verified badge fabricated. |
| 027 | 018 | E / ALL | Real DB migration fault injection before/after commit and competing writer; recover valid owner/version, all original links preserved, no duplicate writer. |
| 028 | 017 | C / ALL | Seeded edit sequences including rule changes, aliases, deletions, negative lookups; compare complete normalized incremental versus uncached graph and diagnostics. Retain seed on failure. |
| 029 | 014 | E / ALL | Repeat structural generation with different run timestamps; byte identity of stable pages, only run-scoped output/latest pointer changes. |
| 030 | 014 | E / GIT | Commit generated output, regenerate at new tree identity; declared input identity excludes self-output so bytes stabilize without endless commit/hash churn. |
| 031 | 002,003,004,005,006,007,014 | E / ALL | Real feature has each relationship kind plus irregular origin; rendered Markdown lists every requirement/AC, verification kind, target, provenance and unresolved diagnostics. |
| 032 | 020 | V / UI | Open generated HTML via file URL with network disabled; navigation works; script/event-attribute/URL payloads stay inert in real browser capture. |
| 033 | 015,016 | V / UI | Shared component under two feature/layer branches; selection events resolve same canonical graph/detail identity without duplicate nodes. |
| 034 | 015,020 | V / UI | Capture old revision evidence then edit current source; inspector opens retained old bytes with exact revision and no silent worktree fallback. |
| 035 | 015,020 | V / UI | Drop/reorder delta, wrong base digest, malformed SDN; resync requested; last-valid revision remains visibly stale, never current green. |
| 036 | 015 | V / UI | Keyboard-only tree/pane/graph/source traversal, expansion/back/forward and live refresh; accessibility/focus observations verify reachable actions and preserved focus. |
| 037 | 013,015 | V / UI | Graph exceeds display budget with failing obligation outside view; hidden count visible and full qualification remains failed. |
| 038 | 010,017 | P / ALL | Cold/warm/high-fan-out fixtures with >=30 ordinary samples; independent elapsed/RSS receipts, p50/p95/p99, hits/files/bytes/closure; deadlines produce incomplete. |
| 039 | 002,013,019 | E / ALL | Draft feature with unsatisfied obligations then completed-state request, unauthorized request, fully satisfied authorized request, later source edit; only authorized complete eligible state qualifies and later edit invalidates it. |
| 040 | 020 | V / UI+ALL | Private/public entities, traversal/symlink/absolute-path source requests and export; allowed content visible, forbidden source/artifact never published or arbitrarily read. |

## Self-traceability and development coverage beyond the 40 rows

Family S must exercise this feature itself, through production extractor, resolver, runner and report writer. These are additional scenarios, not newly invented normative requirement IDs:

1. Enumerate REQ-TRC-001 through 020 and AC-TRC-001 through 040 from structured authored declarations; all resolve to planned scenarios and implementation obligations. Compare against an independent fixed expected set, not whichever IDs happened to parse.
2. Trace report/research -> architecture/detail design -> acceptance -> unit/IT/component -> implementation, including the graph's own shared module and explicit exception. Missing development artifact is an obligation, not an inferred pass (REQ-002,003,005,013,016).
3. Check pre-implementation state: fail-fast placeholders are visible as failing/unimplemented, and authored manual presence never grants execution coverage (REQ-013).
4. Execute real acceptance-only self-run, retain immutable SDN/Markdown on success and deliberate failure; lower layers remain NOT RUN until separately executed (REQ-012,013).
5. Update the checker source, rule/schema, and its own requirement independently; invalidate old self-evidence. Trusted checker admission must not accept a candidate's self-asserted PASS (REQ-011,013,017).
6. Generated manuals and structural trace pages agree on exact criterion IDs, source revision and observed validity; no manual bootstrap circularity, self-hash loop, or generated-output-only qualification (REQ-014,020).
7. Genuine release/feature completion checks all mandatory host/capability rows, outstanding exceptions, reviewer authorization and generated-manual quality; postponed work stays blocked (REQ-019).

## Production seams and prerequisites found

- `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`: `RunnerTestDb.load`, `start_run`, `update_test_result`, `complete_run`, `save`, and `record_resource_run` wrap the unified `std.database.test_extended.TestDatabaseExtended` owner. Extend this boundary; do not create a parallel evidence database writer. Existing completion counters alone cannot prove required shard completeness or artifact provenance.
- `src/lib/nogc_sync_mut/test_runner/main.spl` imports the compatibility owner. `test_runner_helpers.spl` loads it. Verify the actual selected runner path: comments in `test_runner_modes.spl` still mention disabled DB imports, so mere API availability does not prove production invocation.
- `src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl`: reuse `build_interpreter_result_wrapper` for diagnostic interpreter runs and `preprocess_spipe_native_result_file` for native preprocessing. Inspect executed count and matcher exit status; outer compile/summary PASS alone is insufficient.
- `src/app/spipe_docgen/spipe_docgen/evidence_loader.spl`: `load_evidence_fragment` reads a sidecar described as key/value lines, explicitly not full SDN. Needs schema migration/provenance validation; `.sdn` filename is not proof of compliant serialization.
- `src/app/spipe_docgen/spipe_docgen/evidence_manifest.spl`: rendering, path validation, file hash/size helpers exist; its `std.spec.scenario_evidence_manifest` import must be resolved before selecting it as an executable seam. The expected `src/lib/nogc_sync_mut/spec/scenario_evidence_manifest.spl` was absent during inventory. Do not assume every guide example builds.
- The legacy report frontend now uses `traceability_report_to_sdn`; JSON output is rejected. The exact-snapshot preview source routes through `snapshot_preview` and `extract/snapshot_pipeline`, but remains selected-scope and admission-ineligible. Header/path parsing and generated-spec helpers do not establish semantic requirement-to-case coverage.

This isolated worktree did not expose a `bin/release` host directory during inventory. Before running acceptance, identify a deployed pure-Simple self-hosted executable, version/provenance/digest, matched libraries and selected native lane. Do not substitute a seed or bootstrap stage3 artifact. Do not start a cold bootstrap merely to paper over a missing deploy; coordinate with runtime owner and retain an explicit blocker.

## Host execution and resource plan

Run native suites sequentially where they share the test DB. Each host must provide Git, an isolated writable fixture root, native self-hosted executable, capture tools for its declared UI backend, and independent wall/resource measurement. JJ/SJ rows add exact version/transport and publication adapter. Remote rows need an isolated non-publication harness with trusted checker/policy identities and all four event subjects. Never invoke real pushes or policy weakening merely to test fixtures.

Record host, architecture, OS/filesystem case behavior, binary digest, input snapshot, rules/policy version, fixture seed, command, timestamps, discovered/executed counts, attempts, exit, artifacts and their hashes. Unsupported capability rows require a reviewed scope decision, not a successful skip.

Performance targets from report section 19: commit p95 <=500 ms / p99 <=1 s for <=25 relevant files and <=2 MiB warm input; warm push trace incremental p95 <=2 s; full local gate target <=10 s; warm remote trace contribution <=5 s; remote processing target <=60 s; 1,000-observation report <=2 s; loaded Slop selection <=150 ms; useful initial graph <=200 visible nodes with truthful hidden counts. Measure RSS rather than inventing a numeric memory limit absent an approved target. Separate cache-cold and high-fan-out distributions, and record explicit escalation outcomes.

## Review and stopping rules

Plan existence is not test execution. Before qualification, attach each row's real receipt or a linked TODO recording owner, missing prerequisite, exact resume command with resolved binary and fixture paths, and retained artifacts. A generic command template is not an executable resume command. The merge owner must resolve planned family paths to actual tests and retain all AC associations even when splitting files.

Verify a criterion once after the relevant change converges; rerun only after a material fix invalidates that result. At most three verify/fix cycles. Stop after convergence, or report blocked rows. Run direct-env working/staged audits and required compiler/lib/MCP checks when their scopes change. Confirm zero `*_spec.spl` under `doc/06_spec` before committing. No release completion, cross-host PASS, or merge readiness can be inferred from this inventory alone.
## Additional development and delivery acceptance obligations

Original AC-TRC-001..040 remain unchanged. The following named obligations extend their implementation verification; they do not silently replace or narrow the report.

| Additional obligation | Existing requirement links | Real oracle / evidence |
|---|---|---|
| DEV-SELF-GRAPH | 002,003,005,016 | This feature's own structured REQ/AC declarations resolve research, design, acceptance, lower layers, implementation and shared component with no invented execution. |
| DEV-KNOWLEDGE | 002,007,014 | Operational guide and expert knowledge explain SDN-only contracts, exact snapshot, troubleshooting and resume steps; links resolve to the implemented revision. Independent manual review is recorded. |
| DEV-MANUAL | 012,014,020 | Generate manuals from executable modern SSpec; compare actual steps/captures, exact IDs and evidence status; screenshots/text artifacts exist with valid digests. File presence alone fails the criterion. |
| DEV-NATIVE-PROVENANCE | 011,013 | Resolve binary path/digest/build lineage, confirm admitted pure-Simple Stage 4 execution and runtime library match. Wrapper name or version string alone is insufficient; Rust fallback is prohibited. |
| DEV-RUNNER-CALIBRATION | 012,013 | Deliberate matcher failure and zero-executed fixture both produce non-green authoritative results before acceptance evidence is admitted. |
| DEV-REVIEW-LAND | 011,019 | Exact-head PR diff/review, comments resolved, required checks genuinely satisfied and actual merge SHA retained. An open/draft PR is not completion; no tag or publication without release authorization. |
| DEV-HOST-RECEIPTS | 010,013,017,020 | Each required Linux/macOS/Windows and supported UI/jj/SJ capability has native receipt or explicit blocking TODO with owner/prerequisite/exact resume command; postponement is not qualification. |

## Runner path correction and concrete integration contract

The live CLI path is `src/app/test_runner_new/test_runner_main.spl`; `std.test_runner.test_runner_main` is a deduplication facade. The app really calls `update_test_database` in `test_runner_helpers.spl`. Commented calls in legacy `test_runner_modes.spl` do not prove live DB persistence is disabled.

The DB child still starts a run after execution, writes per-file aggregates, completes, then saves. The 2026-10-11 source now persists before SPipe docgen, propagates trace-mode infrastructure failures, and retains actual summaries after renderer failure. Frozen intent is not yet durably saved before dispatch, so these source corrections do not establish the full crash/failure contract. None has native execution evidence yet.

The actual per-case callback is `src/lib/nogc_sync_mut/spec.spl::_execute_it`: `full_name`, pending-before state and local pass/failure decision are known immediately after each body. Its current `_write_test_result_evidence` writes only a `simple-bdd-v1` aggregate tally. Do not reconstruct case observations from that tally or human output. Single-file and ordinary execution paths configure `SIMPLE_TEST_RESULT_FILE` independently; daemon/native/fork/worker paths must explicitly carry case events or remain unsupported/incomplete.

Required transaction sequence: admitted owner freezes case plan + subject/config/binary/expectation manifests and persists a running run before dispatch; framework emits actual case-start/case-finish events through a bounded SDN transport; parent matches events to frozen case IDs, validates producer/artifact lineage and writes immutable attempts through RunnerTestDb; finalizer records exact completed shards and preserves partial observations; persist results before docgen; retain `report_generation_failed` without erasing original failures; crash recovery leaves unfinished rows incomplete. Candidate-provided SDN cannot construct AdmissionContext. Until these adapters execute against native fixtures, pure evaluator results are only kernel evidence.
