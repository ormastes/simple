# TODO — Migrate remaining untyped-evidence candidates onto `untyped_capture.spl`

- Status: open, bounded, in progress. 37 of 1119 candidates migrated ("yes"),
  159 explicitly rejected with recorded reasons ("reject: ..."), as of
  2026-08-09 (batches 1-10 landed, plus the T4 NVMe cluster resolved).
- Owner module: `src/lib/common/spec/evidence/untyped_capture.spl` (landed).
- Design: `doc/05_design/infra/sspec/untyped_evidence_migration_design.md`.
- Guide/worked examples: `doc/07_guide/infra/sspec_legacy_migration.md`.
- Candidate list (regenerate before each session): `doc/08_tracking/audit/untyped_evidence_migration_candidates_2026-08-08.md`.
- Exact resume command to regenerate the candidate list:
  `sh scripts/check/scan-untyped-evidence-candidates.shs`
- Migrated so far (do not re-flag): `test/01_unit/app/io/process_ops_ext_spec.spl`,
  `test/01_unit/app/io/timeout_spec.spl`, `test/01_unit/app/arch_check_spec.spl`,
  `test/01_unit/app/bug_add/bug_add_cli_spec.spl`,
  `test/01_unit/app/bug_resolve/bug_resolve_cli_spec.spl`,
  `test/01_unit/app/io/file_shell_exec_spec.spl` (plus 4 `legacy_facade.spl` migrations
  tracked separately: `lab_html_render_spec.spl`, `scenario_helpers_spec.spl`,
  `legacy_facade_spec.spl`, `scenario_evidence_spec.spl`).
- Per-candidate triage rule (do not skip): read the actual `it` block; confirm it is a
  REAL capture (process/file/network) followed by a substring/exact assertion, not an
  in-memory comparison or a static-source-text read. Reject liberally — a wrong migration
  is worse than a skipped one. Measured yield rate: 5/8 in the first worked batch, 1/24
  in the most recent batch (the easy front-loaded wins are exhausted; remaining rows skew
  toward the scanner's known false-positive class of static `file_read` checks).
- Resume: pull the next unmigrated block of rows from the candidate list (in file order),
  apply the triage rule per-candidate, migrate additively (never remove/weaken an existing
  assertion), verify the full file's example count is unchanged except for the new check,
  sabotage/revert at least one new check per batch, land with the audit doc's migrated
  column updated for every row touched.
- **Yield is now effectively exhausted by sequential scanning (measured 2026-08-09).**
  Batch 10 sampled 15+ unmigrated rows across 6 files in the 40-60% band of the list and
  found ZERO genuine category-1 candidates — every one was category-2 (in-memory, no
  capture) or already-failing. Combined with the per-batch trend (5/8 -> 1/24 -> 0/26 ->
  1/41 -> 7/15 -> 0/15), the remaining ~939 unmarked rows are dominated by the scanner's
  known false-positive class: a spec that `file_read`s a SOURCE file and asserts on its
  literal text (static authorship, never a live observation).
  **Recommended change of approach before spending more sessions here:** stop walking the
  list in file order. Either (a) tighten `scripts/check/scan-untyped-evidence-candidates.shs`
  to exclude the static-source-text class outright and regenerate a much smaller, higher-
  precision candidate list, or (b) spot-sample several regions first and only work bands
  that show real hits. Sequential batches are now mostly paying to re-confirm rejects.
- This has no natural single-session completion point at the current per-batch rate; it is
  designed to be worked incrementally across multiple sessions.
