# trace matrix/links/explain/diff/report: no passing-evidence source wired to the CLI

Status: partly closed 2026-11-16 (opt-in `--evidence=testdb`); end-to-end Verified still needs plan-bound runs in the repo DB.

## Closed
`simple trace matrix|links|explain|diff|report --evidence=testdb` now reads `doc/08_tracking/test/test_db.sdn` read-only
(`open_test_db_read_only`, never saves/seals/migrates) and passes a real `[TracePassingEvidenceV1]` to the existing
status derivation. Default is `--evidence=off`: output unchanged, nothing is `Verified`.
- Pure rule: `src/lib/common/traceability/passing_evidence_v1.spl`
- Loader: `src/app/traceability/query_evidence_testdb_v1.spl`
- Rule: a requirement is evidenced when every spec that verifies it (graph `verified_by` edge via its file locator, or sidecar
  `verified_by` row) has all observed cases passing in their LATEST attempt (later run, then higher ordinal) of a run whose frozen
  plan `subject_id` equals `graph.subject.snapshot_id`. Skipped/cached/failed/unfinished/unknown, runs without a plan, rows
  without a planned-case or attempt identity never count.

## Field availability (what `RunnerTestDb.query_case_attempts` / the DB give)
| Field | In code | Populated in repo `test_db.sdn` |
| --- | --- | --- |
| (a) case identity (path + name, planned case id) | yes, `TestQueryRow.case_key`, `planned_case` | no |
| (b) backend | no field anywhere (`lane_id`, `configuration_id`, `binary_id` on the plan are free text, not a backend set) | no |
| (c) pass/fail/skip/cached | yes, `TestQueryRow.status` / `qualification` | no |
| (d) source snapshot | not on the row; only `TraceRunPlan.subject_id` via `get_trace_run_plan(run_id)` | no |
| (e) pre-fix vs post-fix | no | no |
| (f) case -> requirement | not in the DB; join is graph `verified_by` -> spec path -> plan case path | n/a |

The repo DB holds only `strings, files, tests, suites, resource_runs`: no `trace_case_events`, `trace_run_plans`, or runs table.
Confirmed 2026-11-16, so `--evidence=testdb` currently yields no evidence on the real file; only fixture DBs demonstrate Verified.

## Remaining
- Nothing writes a frozen plan in an ordinary `bin/simple test` run (`test_runner_helpers.spl` records plans only when a
  `trace_run_id` is supplied), so the repo DB never gets `trace_run_plans`/`trace_case_events`. Unblock: a runner lane that
  freezes a plan (subject = worktree snapshot id) for the specs under trace.
- Join granularity is the spec file (the graph has no case-level `verified_by`); `graph.test_definitions` is never filled from
  `trace_sspec_definition_id`, so a definition-id join is not available.
- Specs reached only via acceptance criteria (`accepted_by` / `decomposes_to`) are not evidenced.
- `matrix --filter`, `--format=md|html` for `report`, `links --scope=doc` Markdown/SDN link lint (plan 6.3,
  `src/app/doc/semantic_link_lint.spl`); `links --check` verifies graph edges only.
