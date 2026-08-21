# Perf-fix regression-test audit — 2026-08-21

Scope: perf/slow/quadratic/hang/cache/RSS commits since 2026-08-14, plus the
`doc/08_tracking/bug/` records they cite. Networking/sftp quadratic accumulators
(owned by another session) and the stage3 SEGV / unresolved-symbol guards (not
perf) are excluded.

Question per item: **would a test FAIL if this fix were reverted?**

| # | Item | Fix commit | Test / gate | Kind | Added? |
|---|------|-----------|-------------|------|--------|
| 1 | Per-call env rebuild O(globals) -> CowEnv scope chain | e73a0bec647 | `src/compiler_rust/compiler/tests/interpreter_call_env_o_args.rs` (ratio < 3.0 at 200 vs 4000 globals) | mechanism | pre-existing |
| 2 | Dirty-global patching into cached call-env templates | 408fb57b109 | superseded 4h later by e73a0bec647 (function_exec rewritten, -682 lines); item 1's test covers the same scenario | mechanism | n/a — superseded |
| 3 | HIR frozen-registry owner-scan memos | a865dced154 | `test/01_unit/compiler/hir/hir_package_dependency_scan_memo_spec.spl` | mechanism | pre-existing |
| 4 | Frozen surface registry indexed by decl name/package | 5c783d9935d | same spec (+26 lines in the commit) | mechanism | pre-existing |
| 5 | Registry keys via built-once name index | 331c7d16d54 | same spec (+10 lines in the commit) | mechanism | pre-existing |
| 6 | Native object cache never persisted entries | 809ce6d4e71 | `test/02_integration/compiler/driver/native_build_cache_second_build_hits_spec.spl` | mechanism | pre-existing |
| 7 | Env-template cache invalidated by every method self-update | 2a7a98dafd3 | `test/.../interp/push_call_loop_env_cache_spec.spl` | mechanism | pre-existing |
| 8 | Level-gated interpreter perf counters + nested-if fixtures | 01a3fa7e90d | `test/fixtures/perf/nested_if_{120,240}.spl` | budget | pre-existing |
| 9 | Loader all-i64 exec-memory write (48-164x) | 492a38a7294 | `test/.../loader/exec_memory_bulk_write_spec.spl` | mechanism | pre-existing |
| 10 | Lint dup-typed-args scan: native `find()` instead of per-char loop | 8d3b7d009b9 | **MISSING** -> `scripts/check/check-perf-regression-tests.shs` rows 9-11 | mechanism | **added** |
| 11 | Test-runner daemon backlog bypass wiring | 7a6f6459a81 | policy spec existed; the **call site** was unpinned -> gate row 7 | mechanism | **added** |
| 12 | Two O(n^2) steps removed from test-manifest reindex | 8f3efdfbd65 | **MISSING** -> gate rows 1-6 | mechanism | **added** |
| 13 | Lint cost budget | `.claude/rules/commands.md` | `scripts/check/check-lint-cost-budget.shs` | budget | pre-existing |
| 14 | Hardening perf baseline (wall/RSS fixtures) | 2fd286ab7b6 | `scripts/check/check-hardening-perf-baseline.shs` | budget | pre-existing |

## Finding: item 12 had already been REVERTED on `main`

`8f3efdfbd65` (2026-08-18) replaced two linear `manifest_find_entry` /
`manifest_find_sdoctest_entry` scans with a path->index dict, and moved two
struct-field `.push()` accumulators into locals. `f13adc2eca5` clobbered **both**
with a stale snapshot while adding an unrelated forward change
(`mode_filter.extract_directive_lines`). `main` carried the quadratic reindex —
the one that made `bin/simple test` sit at `[setup] discover: begin` for >1900s —
for three days, with every pre-push guard green, because no guard knows what a
fix was *for*.

The fix is re-applied in this change (on top of `f13adc2eca5`'s forward change,
which is preserved) and pinned by the new gate.

## Gate

`scripts/check/check-perf-regression-tests.shs` — 16 mechanism rows, fail-closed,
`--selftest` (6 fixtures, 3 expected failures) runs first and is fatal, verdict is
the last stdout line, 0 rows is ERROR not PASS.

Verdicts measured 2026-08-21:
- working tree (post-fix): `PASS — 16 mechanism(s) checked, 0 regressed`
- scanner at the clobbered blob `f13adc2eca5`: `FAIL — 16 checked, 6 regressed`
- rules.spl at `8d3b7d009b9~1` and client at `7a6f6459a81~1`: `FAIL — 16 checked, 4 regressed`

Wall-clock budgets were deliberately NOT used for these rows: this host runs
20-30 concurrent `simple` processes and a timing threshold generous enough not to
flake is too generous to catch a 5.7x text-tier regression. Mechanism pins are
deterministic and would have caught the item-12 clobber the hour it landed.
