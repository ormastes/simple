# Feature expert: TestDB passing evidence for `simple trace`

Plan: `simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md` sections 3.5, 4.2-4.4, 6 (advisory per section 11).
Sibling: `doc/00_llm_process/feature_expert/trace_matrix_links_explain/skill.md`.

## Where things live
| Concern | File |
| --- | --- |
| Pure projection attempts -> `[TracePassingEvidenceV1]` | `src/lib/common/traceability/passing_evidence_v1.spl` |
| Read-only loader (runs, frozen plans, attempt rows) | `src/app/traceability/query_evidence_testdb_v1.spl` |
| `--evidence=testdb\|off` option and wiring | `src/app/traceability/query_cmds_{options,main}_v1.spl` |
| Row source (reused, not changed) | `RunnerTestDb.query_case_attempts`, `open_test_db_read_only` |

## Contracts to keep
- Default is `--evidence=off`: output is byte-identical to before; nothing reaches `Verified`.
- Snapshot comes only from the frozen plan (`TraceRunPlan.subject_id`), compared with `graph.subject.snapshot_id` (same identity space as `obligations.spl:117`). A run with no plan has no snapshot and is never evidence.
- Latest attempt wins: later run (by `RunRecord.start_time`), then higher attempt ordinal. Only `qualification == Pass` counts; skipped, cached, failed, unfinished, unknown never do.
- Requirement -> spec join is by spec file path (graph `verified_by` edge through its file locator, plus sidecar `verified_by` rows). A requirement is evidenced only when it has at least one verifying spec and every observed case of every such spec passed. Acceptance-criterion routes are not evidenced.
- The loader never saves, seals, migrates or creates the database; an unreadable store is a typed error and exit 2.

## Verify
`bin/simple test test/01_unit/lib/common/traceability/passing_evidence_v1_spec.spl test/01_unit/app/traceability/query_evidence_testdb_spec.spl test/01_unit/app/traceability/trace_cmds_options_spec.spl`

Open work: `doc/08_tracking/bug/trace_cmds_no_passing_evidence_source_2026-11-15.md`, `doc/08_tracking/bug/bug_closure_gate_wiring_remaining_2026-11-14.md`.
