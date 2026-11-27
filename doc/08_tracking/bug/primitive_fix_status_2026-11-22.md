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

## Not done (initial 2026-11-22 handoff snapshot — updated below)

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

## Updated 2026-11-23 (`work/primitive-fix-20261122`)

### Completed on this branch

- **2a (post-rebase + sync/async parity)**: verified after rebase with `TestSourceRevision`
  re-exported in both sync and async `src/lib/nogc_{sync,async}_mut/database/test_extended/__init__.spl`
  (plus `test_run_source_revision_spec.spl`, `test_extended_async_facade_newtypes_spec.spl`).
- **2b & 2c (observed TestDB bug-closure evidence)**: implemented in `src/app/bug/closure_testdb.spl`,
  `src/app/bug_resolve/closure_cli.spl`, `src/app/bug_resolve/main.spl`, and
  `src/app/bug_closure_check/main.spl` (`5dd48e69674`). Pre-fix and post-fix run IDs and
  `run_source_revision` map into `BugTestRunV1` for `bug_closure_evaluate_v1`.
  Verified (`bug_closure_testdb_spec` 5/5, `bug_closure_wiring_spec` 8/8,
  `bug_closure_gate_spec` 11/11, `bug_add_resolve_log_modes_spec` 12/12,
  `bug_resolve_cli_spec` 4/4).
- **Item 3 (TestDB / `ResourceUsage` record-struct bare primitives)**: replaced bare primitive
  fields with domain wrapper types in `ResourceUsage`, `TestDbFileRow`, `TestDbRunRecord`,
  `execution_metrics`, and `test_extended` record structs (`553dcae1e53`), keeping
  `simple-test-db-record v1` and `execution-metrics-1` wire/SDN serialization unchanged.
- **Item 4 Phase 1 (checker upgrade + traceability/bug sweep)**: upgraded
  `scripts/check/check-primitive-api-added.shs` (`f0833659b6d`) for multi-line signatures,
  `pub(scope)`/`async`/`static`, `?`/`Option<>`/`Result<,>`, `pub struct`/`pub class`/`impl`
  fields & methods, single-field numeric newtype exemption (`bool` flagged), and `git diff -M`
  rename tracking (`--selftest` PASS under BSD `awk` and `gawk`; `--changed origin/release/1.0.0..HEAD`
  PASS across 47 files, 0 added). Swept remaining bare primitives to 0 in
  `src/lib/common/traceability/{envelope_types_v1,codec_fields_v1,codec_text_budget_v1,conventions_result_v1}.spl`
  and `src/app/bug/{workaround_index,workaround_retirement,workaround_revert}.spl` plus callers.
  Verified across traceability specs (101/101), workaround store/autoretire/fragment/revert/system
  specs (44/44), and `mcp_stdio_integration_spec` (16/16). Note: pre-existing unmodified
  failures on `origin/release/1.0.0` remain outside this change in
  `workaround_retirement_spec` (1/5: `workaround_host_temp_dir` returns relative path to
  `snapshot_symlink_create_nofollow_v1`) and `workaround_annotation_format_spec` (1/6:
  27 existing `@workaround` bug IDs in `src/*.spl` absent from `bug_db.sdn`).

### Still open / gated

- **Item 1** (`SIMPLE_TRACE_CASE_EVENTS=1` exit-2 gate in `src/app/test_runner_new/test_runner_main.spl`):
  **STAYS GATED** on the six owner questions above.
- **Item 4 Phase 2**: Remaining public bare primitive slots outside the swept
  testdb/traceability/bug modules (debug contracts, P0 libraries, etc.) remain open.
