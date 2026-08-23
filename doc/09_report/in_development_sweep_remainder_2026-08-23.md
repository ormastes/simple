# In-development tag sweep — slice 4 (remainder), 2026-08-23

**Outcome: 0 specs tagged.** Every directory this slice owns is either fully green
or fails for a reason the `@tag:in-development` mechanism explicitly must not cover.
Stood down mid-sweep on a coordinator capacity call (box at load 64/32 cores, 9 GB
free); the two perf trees are therefore **unmeasured**, not green.

## Directories taken (slice 4 = everything outside slices 1-3)

Enumerated with `find test -name '*_spec.spl' | awk -F/ '{print $2}' | sort | uniq -c`.
Slices 1-3 own `01_unit`/`unit`, `03_system`/`system`, `02_integration`/`integration`/`feature`.
The complete remainder, all of which is mine:

| dir | specs | executed | verdict |
|---|---|---|---|
| `test/05_perf/` | 110 | 0 | **UNMEASURED** — stood down before this tree started |
| `test/perf/` | 39 | 1 | **UNMEASURED** — SIGTERM (rc=143) after spec 1; reaped under load |
| `test/fixtures/` | 25 | 19 | 13 PASS / 6 FAIL — all 6 fail **by construction** (see below) |
| `test/00_formal_verification/` | 22 | 22 | 22 PASS / 0 FAIL |
| `test/shared/` | 21 | 21 | 21 PASS / 0 FAIL |
| `test/tmp_repro/` | 3 | 3 | 0 PASS / 3 FAIL — scratch defect-repro material |
| `test/07_security/` | 2 | 2 | 2 PASS / 0 FAIL |
| `test/_probe_root_tmp/` | 1 | 1 | 1 PASS / 0 FAIL |

Total slice: **223 specs; 69 executed; 9 failing; 0 tagged.**

## Counts

- run: 69 · failing: 9 · **tagged: 0** · left red: 9 · load-failures: 0 ·
  environmental: 0 spec-level (3 harness-level, below) · load-flaky: 0 measured ·
  inconclusive/unmeasured: **149** (both perf trees).

## Why nothing was tagged

- **`test/fixtures/` is not a suite.** Its 6 red specs (`unstable_mode/fail_spec`,
  `_accept_run/fail_spec`, `visibility_test/case_spec`,
  `pure_simple_tooling/{before_hook_failure,sibling_describe_red,earlier_expect_failure}_spec`)
  are *deliberate red inputs* the runner's own tests consume. Tagging them would
  neutralise the fixtures that prove the runner reports failure. Never eligible.
- **`test/tmp_repro/`** (`mir_spec`, `mir2_spec`, `repro_spec`) is scratch
  defect-reproduction material — specs correctly asserting defects. Per
  `.claude/rules/testing.md` these stay RED with a bug record. Never eligible.
- **Perf trees are unmeasured, so no perf verdict was formed at all.** Confirming
  the caution in the brief: `test/perf` executed exactly one spec
  (`compiler_perf_baseline_spec.spl`, PASS) before the process was SIGTERMed.
  Measuring perf budgets on a box at load 48-64 would produce load artifacts, not
  regressions, and neither is in-development work.

## Harness traps hit (all confirmed, none tagged)

1. **`--cpu-threshold=` / `--mem-threshold=` crash the runner.** Passing them
   aborts arg parsing with `error: semantic: cannot iterate over this type`,
   rc=1, **zero specs executed** — a third phantom alongside the `@cover` gate and
   the watchdog. My first batch (`fixtures`, `00_formal_verification`, `tmp_repro`)
   was discarded for this and re-run with `--no-self-protect --no-cover-check`,
   which work correctly. Worth a bug record; not filed here (docs-only landing).
2. **Self-protection watchdog** (rc=42) truncated the first `test/shared` run at
   20/21 specs, as the coordinator warned. Bypassed on the re-run.
3. **`rc` is not a verdict here.** `test/07_security` and `test/_probe_root_tmp`
   are 100% PASS yet exit 1, because the run ends with
   `error[E1002]: function runtime_file_rename not found` during teardown/DB write.
   Only the `  PASS ` / `  FAIL ` per-spec lines were trusted.

## Mirror-tree note (unused, recorded for the next lane)

`test/perf` vs `test/05_perf`: 26 twins byte-identical, 12 already diverged,
1 perf-only (`test/perf` has no `05_perf` counterpart). Any future tagging must
edit the 26 identical twins in both trees together or fail
`scripts/check/check-test-tree-divergence.shs`. No test-tree edits were made.

## Left unfinished

`test/05_perf/` (110 specs) and 38 of 39 `test/perf/` specs were never executed.
They need a quiet box; on the current one no trustworthy perf measurement is
obtainable. Resume state and logs left in place at `/mnt/fast/tagsweep-logs/`
and worktree `/mnt/fast/wt-tagsweep-remainder`.
