# Bug: `--unit` / `--integration` / `--system` filters match ONLY the legacy mirror tree

- **Date:** 2026-07-27
- **Status:** open
- **Severity:** high (level-filtered runs silently select the stale tree, or nothing)
- **Found by:** lane TESTDUP while surveying the duplicate spec hierarchy

## Symptom

`matches_level` / `detect_test_level` classify a spec by testing
`path.contains("/unit/")` (and `/integration/`, `/system/`). Those substrings do
**not** match the numbered directories `/01_unit/`, `/02_integration/`,
`/03_system/`.

Consequences:
- Every spec in the **maintained** numbered tree scores level 0 and is therefore
  invisible to `--unit`, `--integration` and `--system`.
- A level-filtered run selects only the **legacy mirror** — which is stale:
  6,540 of 7,605 mirror `.spl` files are still frozen at their 2026-07-01
  creation date, against 2,760 commits in the numbered tree over 30 days versus
  128 in the mirror.
- So `bin/simple test --unit` is, today, largely a run of a month-old snapshot.

## Why it also blocks a large cleanup

The mirror (`test/unit/`, `test/integration/`, `test/system/`) duplicates the
numbered trees and costs double maintenance — several lanes this session had to
edit both copies of the same spec. Retiring it would remove roughly **11,600
files**, but that is currently **unsafe**:

1. The runner's default discovery is an unfiltered recursive walk of `test/`
   (`test_runner_args.spl:491`, `test_runner_files.spl:297,326` → `rt_dir_walk`),
   selecting on filename only — so both trees are discovered and deleting the
   mirror drops ~7,550 files from the default run.
2. Because of the bug above, deleting the mirror makes every **level-filtered**
   run match zero specs.
3. **655 pairs genuinely diverge** by >10 lines (251 by >50) — real work exists on
   both sides, so they are DIVERGED, not stale.
4. **25 true orphans** exist only in the mirror and are live: a spot check ran
   `test/unit/compiler/verification/naming_spec.spl` → **9 examples, 0 failures**
   with no numbered counterpart. A bulk delete would have silently destroyed 24
   live passing specs (16 `compiler/verification/`, 6 `system/coverage/`,
   `db_server_tier`, `parser_gap`).

Note also that ~5,000 `.txt` files in both trees are committed stale run
artifacts (`summary.txt` carrying Windows paths `C:\Users\...`, `duration_ms: 0`),
not specs.

## Fix

1. Make `detect_test_level` / `matches_level` recognize the numbered prefixes
   (`01_unit`, `02_integration`, `03_system`) as well as the bare names. This is
   the prerequisite for any deletion.
2. Add a spec asserting a numbered-tree path classifies at the right level — the
   absence of one is why this went unnoticed.
3. Then, in order: relocate the 25 true orphans into the numbered tree, resolve
   the 655 diverged pairs, and only then retire the mirror.

Full survey table, orphan list and the 5-step unblock sequence:
`.spipe/test_tree_dedup/state.md`.

## Resolution 2026-11-25 (lane p2w6-ac, base release/1.0.0 `64dfa6d980f`)

**Status: RESOLVED** — fix item 1 is now complete for the last unfixed copy;
fix item 2 (numbered-tree classification spec) already existed.

State found at HEAD:

- `detect_test_level` (`src/lib/nogc_sync_mut/test_runner/test_manifest_scanner.spl:245`)
  already delegates to the segment-based `test_level_of_path`
  (`src/lib/nogc_sync_mut/test_runner/test_level_detect.spl:68`), which
  recognizes both the numbered tree and the legacy mirror — so the manifest
  fast path (`discover_test_files_fast` -> `manifest_entry_matches_level`) was
  already fixed.
- The std copy of `matches_level`
  (`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:261`) was already
  segment-based and spec-covered (fix item 2):
  `test/01_unit/app/test_runner_new/runner_files_filters_spec.spl` asserts
  `test/01_unit/...` -> Unit, `test/02_integration/...` -> Integration,
  `test/03_system/...` -> System.
- The **app** copy (`src/app/test_runner_new/test_runner_files.spl`), still
  used by the no-manifest fallback `discover_test_files_slow`, was NOT fixed:
  it classified with `path.contains("/unit/")` (never matches `/01_unit/`) and
  had no `TestLevel.Smoke` arm.
- The legacy mirror trees `test/unit/` and `test/integration/` no longer exist
  (only `test/system/` remains), so the "level-filtered run selects the stale
  mirror" symptom was already moot on the fast path.

Fix: the app copy now delegates to the same `test_level_of_path` (imported via
the package export `std.nogc_sync_mut.test_runner.{test_level_of_path}`) and
gained the missing `TestLevel.Smoke` arm, mirroring the std copy. Legacy
behaviors are preserved (`shared` -> unit, `feature` -> system) and
`community`/`opportunity` no longer substring-match as unit/system.

Evidence (pinned seed `bin/simple.exe` v1.0.0-rc.1, Windows):

- BEFORE: code inspection of the old substring form at
  `src/app/test_runner_new/test_runner_files.spl:114-123`. A runtime
  BEFORE/AFTER of the app module itself is environment-blocked on this host:
  the pinned seed rejects `@representation_boundary` (added repo-wide by
  cfd89933699) on `file_read_borrowed_bytes` in the module's transitive
  imports, so neither `bin/simple.exe test` nor a direct `run` probe of the
  app module can execute at HEAD.
- AFTER: a probe replicating the fixed function verbatim (same import form,
  same body) runs green under the seed: `test/01_unit` -> Unit true,
  `test/02_integration` -> Integration true, `test/03_system` -> System true,
  legacy `test/unit` -> Unit true, `test/shared` -> Unit true,
  `test/feature` -> System true, `test/04_smoke` -> Smoke true, cross-level
  rejections false, `test/community` -> Unit false. The delegation target
  `test_level_of_path` was also executed directly with the same verdicts
  (1/2/3 for the numbered trees, 1 for the legacy mirror).

Fix item 3 (orphan relocation, diverged-pair resolution, mirror retirement)
is a separate cleanup program tracked in `.spipe/test_tree_dedup/state.md`,
not part of this runner defect.
