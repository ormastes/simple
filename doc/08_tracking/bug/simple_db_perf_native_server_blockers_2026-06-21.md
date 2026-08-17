# Simple DB Perf Native/Server Blockers - 2026-06-21

Goal: embedded and full/server DB CRUD benchmarks should match or beat SQLite
and PostgreSQL where comparable.

Current evidence:

- `sh scripts/check/check-simple-db-perf-compare.shs`
- Embedded runtime: `native_or_direct`
- Server mode: `unavailable`
- Server reason:
  `examples_11_advanced_simple_db_submodule_not_initialized_or_missing_benchmark`
- The embedded compare wrapper now reports positive native/direct timings, but
  the current driver is timing-only because native DB row/scalar materialization
  is still unsafe for full value validation.
- `DbValue.Integer(value: 70)` previously decoded as `8` in native code because
  single-argument enum variants passed raw integer payloads. The lowerer now
  boxes primitive single-argument enum payloads before `MirInst::EnumWith`;
  verified with `src/compiler_rust/target/debug/simple run
  test/05_perf/bench/db_crud_native_probe.spl` reaching `direct_int=70`.
- Native/JIT fallback previously reported and is now cleared in the bounded
  compare wrapper:
  `cannot infer field type while lowering BTree.delete_from_node: struct 'BTreePredEntry' field 'val'`.
  `src/lib/nogc_sync_mut/storage/shared/btree.spl` now has an explicit
  `BTreePredEntry<V>` annotation at that predecessor lookup site; verified with
  `bin/simple check src/lib/nogc_sync_mut/storage/shared/btree.spl`.

Latest bounded strict run:

- `SIMPLE_BIN=src/compiler_rust/target/debug/simple ./scripts/check/check-simple-db-perf-compare.shs`
- Result: `STATUS: WARN simple db perf compare blockers: target_misses server_unavailable`
- Exit: `0`
- Crash: none during the wrapper run
- Wrapper is cwd-independent as of this note; it `cd`s to repo root before
  running commands.
- Blockers emitted by the wrapper now:
  `target_misses server_unavailable`

Measured embedded native/direct timings from the timing-only driver:

- insert_100: `2131us`
- where_pk_param_100: `356us`
- update_100 single-column typed path: `1160us`
- delete_100 typed PK path: `1061us`
- transaction_insert_100: `5572us`

Latest focused native probe:

- Command:
  `src/compiler_rust/target/debug/simple run test/05_perf/bench/db_crud_native_probe.spl; code=$?; echo exit=$code`
- Output reached `probe_present=true`.
- It segfaulted before `probe_cols_len=...` / `probe_len=...` and exited `139`.
- Tiny standalone probes show direct `DbRow`, `DbRow?`, `Result<DbRow?>`, and
  `[DbRow]` class-method returns are safe. The crash remains specific to
  DB-built rows from `PureDatabase`.
- 2026-06-22 follow-up: a local copy-hardening attempt routed direct fast-path
  `DbRow(columns: ..., values: typed[...])` returns through `_row_result`, but
  the bounded native probe still segfaulted and `probe_rows_len` printed a
  corrupt negative value before `DbRow.values` access. That source change was
  rejected to avoid adding hot-path copies without fixing the crash. Treat the
  remaining blocker as native materialization of `Result<[DbRow], DbError>` or
  DB-built `[DbRow]` query result arrays, not only direct `DbRow.values`.
- `test/05_perf/bench/db_crud_compare_driver.spl` uses a temporary timing-only
  scalar gate. Do not treat current embedded timings as final correctness
  evidence until full DB row/scalar validation is restored.
- A bounded typed-path pass replaced update/delete SQL-string timing with
  `update_by_key` / `delete_by_key` timing and added an all-visible typed PK
  delete fast path. This improves update/delete from the earlier ~28ms/~26ms
  range, but still misses SQLite targets.
- A second bounded pass removed unused all-visible update transaction work,
  added a direct single-column typed update helper, and changed delete to
  swap-remove the typed row plus update the moved PK map entry. Update/delete
  improved again but still miss SQLite targets.
- A third bounded pass stopped deferred transaction commit from forcing
  `checkpoint()` and added exact `BEGIN` / `COMMIT` / `ROLLBACK` command
  shortcuts before normalized parsing. Transaction insert improved slightly, but
  still misses both SQLite and PostgreSQL targets.

Required before completion:

- Run the same harness without interpreter fallback.
- Fix the native `DbRow.values` access crash shown by
  `test/05_perf/bench/db_crud_native_probe.spl`.
- Restore full value validation in
  `test/05_perf/bench/db_crud_compare_driver.spl` after DB row materialization
  is safe.
- Provide or wire full/server-mode DB benchmark command via `SIMPLE_DB_SERVER_BENCH_CMD`.
- `sh scripts/check/check-simple-db-perf-compare.shs --strict` must pass.

Crash-safety note:

- Do not loop native/release rebuilds while investigating this; run one bounded
  native check at a time and stop on segfault/core-dump/fallback.

---

## 2026-08-17 — no *silent* fail-open found; the exit-0 is labelled and deliberate. Row re-scoped, one residual gap named.

Audited `scripts/check/check-simple-db-perf-compare.shs` for the fail-open class
(a vacuous run reported as a pass). It does not have one in the silent sense:

- `strict_blockers()` (lines 82-101) explicitly enumerates
  `invalid_or_missing_rows`, `target_misses`, `interpreter_fallback` and
  `server_unavailable`, and returns the literal `none` only when all four are
  clear.
- The non-strict default (`SIMPLE_DB_PERF_STRICT=0`) prints
  `STATUS: WARN simple db perf compare blockers: <list>` as the **last line of
  stdout** and exits 0. That is an exit 0, but it is not a claimed pass: the
  verdict line says WARN and names every blocker. `STATUS: PASS` is printed only
  on `none`.
- `--strict` / `SIMPLE_DB_PERF_STRICT=1` turns the same blocker set into
  `STATUS: FAIL` exit 1.
- A completely failed embedded run still surfaces: `run_mode` records
  `embedded_status=failed`, every `baseline_row` value degrades to `-`,
  `status_vs_baseline` returns `missing`, and `invalid_or_missing_rows` fires.
  A driver that exits 0 while printing no timings degrades along the same path.

So the row's substance ("server lane and value validation remain open") is a
**coverage gap, not a false green**, and I did not reproduce a run that reported
success while checking nothing. **No code change made.**

Residual gap worth stating rather than papering over: the script has **no
`--selftest`**, so the blocker-classification logic above is unverified — nothing
would catch a future edit that made `strict_blockers()` return `none`
unconditionally, and that *would* be a silent green in the strict lane. Adding
`--selftest` fixtures over `strict_blockers()` (one per blocker category, plus an
all-clear control and an empty-input non-vacuity case) is the natural next step;
it was not done here because this row is P3 and the two P2/P3 rows in the same
slice had reproducible defects that took priority.

Also unproven: I did not execute the lane (it runs a native benchmark and a
bootstrap was live on this host), so the *measured* server/value-validation
status is unchanged from whatever the doc last recorded.
