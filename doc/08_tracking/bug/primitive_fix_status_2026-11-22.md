# primitive_fix — status handoff (2026-11-22)

Branch `primitive_fix` is based on `origin/release/1.0.0` and carries the
unlanded work for the traceability / bug / MCP plan
(`simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md`)
and the public-primitive cleanup. Nothing here has been reviewed or merged.

## On this branch

1. **feat(testdb): source revision per test run (plan 4.2/4.3, item 2a)**
   - `src/lib/nogc_sync_mut/database/test_extended/source_revision.spl`:
     `TestSourceRevision`, `test_source_revision_of`, `current_test_source_revision`.
     A run records a revision only when git answered, the id is 40/64 lowercase hex,
     and the tracked tree is clean.
   - `database.spl`: `source_head` column, `start_run(source)`, `run_source_revision(run_id)`.
   - The test runner records `current_test_source_revision()` at run start.
   - Spec `test/01_unit/lib/database/test_run_source_revision_spec.spl`.
   - Verified before the rebase: 4/4. Sabotage (dirty check ignored, store dropped)
     fails 3/4 each; revert gives 4/4. Regression specs green: primitive_types 7/7,
     trace_run_preparation 12/12, test_db_integrity 27/27, test_query_cli 26/26,
     cold_start 3/3, async facade newtypes 3/3.
   - Rebased onto the release line, where the `test_extended.spl` facade files were
     deleted; the exports now go in `test_extended/__init__.spl` (sync and async).
     **Not re-run after the rebase.**
2. **docs(trace): binding source/options to trace preparation.** Design only; the
   exit-2 gate stays as-is.

## Not done

- **2b** closure requests carrying the pre-fix and post-fix run ids
  (`src/app/bug_resolve/closure_cli.spl` `BugClosureRequestV1`).
- **2c** mapping TestDB runs (with `run_source_revision`) into `BugTestRunV1`
  (`src/app/bug/closure_gate.spl:118`).
- **Item 1** exit-2 trace gate: blocked on six owner questions (does a fixed trace
  timeout override `@timeout`; is the cache forced off; which env vars are bound;
  are feature-gated specs refused; frozen source as an owned copy or a re-hash;
  are interpolated case names refused).
- **Item 3** TestDB record fields (`ResourceUsage`, `TestDbFileRow` and similar
  types): not started. The earlier agent left no diff.
- **Item 4** bulk public-primitive sweep: census only. 21,155 primitive slots in
  2,858 files: 9,787 `pub fn`, 9,561 public struct fields, 1,807 methods in public
  types without `pub`. `scripts/check/check-primitive-api-added.shs` misses
  multi-line signatures, qualified names, fields and renames; extend it before the
  sweep. Suggested order: trace/xray, then bug/testdb/MCP, then debug contracts,
  then the P0 libraries.
