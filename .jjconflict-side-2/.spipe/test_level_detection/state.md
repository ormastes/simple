# Lane LEVELFIX — test-level detection sees the maintained numbered tree

- **Date:** 2026-07-27
- **Bug:** `doc/08_tracking/bug/test_level_filters_never_match_numbered_trees_2026-07-27.md`
- **Status:** fix implemented + spec added + payoff measured. NOT committed (lane is no-commit).

## What was wrong

`detect_test_level` and `matches_level` classified a spec by loose substring
(`path.contains("/unit/")`, `"/integration/"`, `"/system/"`). Those substrings
never match the maintained numbered directories `test/01_unit/`,
`test/02_integration/`, `test/03_system/`, so `--unit` / `--integration` /
`--system` selected essentially only the stale legacy mirror.

## Change

New pure module (no `extern`, no I/O, so specs can import it directly):

- `src/lib/nogc_sync_mut/test_runner/test_level_detect.spl`
  - `strip_order_prefix(seg)` — `01_unit` -> `unit`; only the exact `NN_` shape
    is stripped (`1_unit`, `_unit`, `ab_unit` pass through).
  - `path_level_segments(path)` — normalizes `\` to `/`, splits, strips prefixes.
  - `path_has_level_segment(path, name)` — whole-SEGMENT match, not substring.
  - `test_level_of_path(path) -> i64` — 0 none / 1 unit / 2 integration /
    3 system. Priority order preserved from the original implementation
    (unit, then integration, then system|feature, then shared).
  - `test_level_matches(path, level_code)` — code 0 means all levels.

Call sites rewired (behavior otherwise unchanged):

- `test_manifest_scanner.spl::detect_test_level` -> delegates to `test_level_of_path`.
- `test_runner_files.spl::matches_level` -> delegates to `test_level_matches`.
- `execution_strategy.spl::<test category>` -> `path_has_level_segment` for the
  integration/unit/system/shared arms (same bug class; picks the execution
  strategy and timeouts for numbered-tree specs).
- `src/lib/nogc_sync_mut/test_runner/__init__.spl` — new re-export block.

`src/app/test_runner_new/__init__.spl` and the `nogc_async_mut` /
`gc_async_mut` test_runner dirs are thin re-export shims — no edit needed.

### Other levels

`TestLevel` has only `All/Unit/Integration/System`. `00_formal_verification`,
`04_smoke`, `05_perf`, `06_fuzz`, `07_security`, `08_web_platform`,
`09_baselines` have no enum variant; after prefix stripping they normalize
identically to their bare counterparts (`smoke`, `perf`, ...) and stay
unclassified (0) — same as before, now consistently across both trees.

## Spec

`test/01_unit/test_runner/level_detection_spec.spl` — 8 describes covering:
numbered tree (`01_unit`/`02_integration`/`03_system`), bare mirror
(`unit`/`integration`/`system`/`feature`/`shared`), Windows separators,
`--unit`/`--integration`/`--system` filter mapping, and NEGATIVE cases proving
`opportunity`, `community` (contain `unit`), `ecosystem` (contains `system`),
`disintegration` (contains `integration`) and a `unit_helper_spec.spl` basename
do NOT misclassify.

## Verification

- Spec, JIT engine: `bin/simple run test/01_unit/test_runner/level_detection_spec.spl`
  -> 8 describe blocks, **19 examples, 0 failures**.
- Spec, interpreter engine (`SIMPLE_EXECUTION_MODE=interpreter`): same, 0 failures.
- Rewired call sites, live behavior: `build/levelfix_probe/check_matches_level.spl`
  exercises `matches_level`, `detect_test_level` and `categorize_test_file`
  through their real modules — all 10 assertions match expectation
  (`matches_level("test/01_unit/app/cli_spec.spl", Unit) = true`,
  decoy `test/app/opportunity/...` = false, `categorize_test_file` on
  `01_unit`/`02_integration` returns `unit`/`integration`).
- Lint: `test_level_detect.spl` + the new spec -> "Lint passed: all files clean"
  (0 errors; 16 `spipe_missing_docstrings` warnings, matching the existing style
  of the sibling specs in that directory).
- Lint on `test_runner_files.spl` (COLL006 string-concat-in-loop) and on
  `execution_strategy.spl` (`method 'get' not found on type 'str'` +
  `pp[...]` generics) reproduce **identically on `git show HEAD:<file>`** —
  pre-existing, not introduced here.

## Payoff (measured)

Probe: `build/levelfix_probe/count_levels.spl` — walks `test/`, classifies every
`*_spec.spl` with the OLD substring predicate and the NEW segment predicate.

```
total *_spec.spl under test/: 23896
--unit          OLD=5054  NEW=16004
--integration   OLD=640   NEW=1718
--system        OLD=3363  NEW=5912
numbered tree only (01_unit / 02_integration / 03_system):
  --unit        OLD=25    NEW=10975
  --integration OLD=27    NEW=1105
  --system      OLD=1168  NEW=3717
non-numbered specs still matching --unit (mirror + shared): 5029
```

The numbered-tree OLD counts are not literally zero only because of nested
`.../unit/`, `.../system/`, `.../feature/` subdirectories inside the numbered
tree; the top-level numbered dirs themselves matched nothing.

## Mirror retirement

Prerequisite 2 of the bug doc ("deleting the mirror makes every level-filtered
run match zero specs") is now DISCHARGED: after this change a level-filtered run
selects 10,975 unit / 1,105 integration / 3,717 system specs from the numbered
tree alone.

Still blocking retirement:
1. **25 true orphans** live only in the mirror and pass (16 `compiler/verification/`,
   6 `system/coverage/`, `db_server_tier`, `parser_gap`) — relocate into the
   numbered tree first.
2. **655 diverged pairs** (>10 lines; 251 >50) — real work exists on both sides,
   must be merged, not deleted.
3. Default discovery is still an unfiltered recursive walk of `test/`, so the
   unfiltered default run drops ~7,550 files on deletion — expected, but should
   be an intentional, announced drop.

## Not done here

- No commit/push (lane constraint).
- `src/lib/*/process_limits.spl:134`, `src/app/check_skip/main.spl:96`,
  `src/compiler/35.semantics/lint_cross_ref.spl:43` and
  `.../dashboard/collectors/spipe_collector.spl:138` carry the same
  `contains("/unit/")` pattern for unrelated purposes (timeouts, lint, dashboard)
  and are outside this lane's owned paths. They have the same numbered-tree
  blind spot and should be swept next.
- Deployed `bin/simple` here is the Rust bootstrap seed; the compiled runner in
  the deployed binary still carries the old logic until a rebuild/redeploy, so
  `bin/simple test --unit` only picks the fix up after the next bootstrap.
