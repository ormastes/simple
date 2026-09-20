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
