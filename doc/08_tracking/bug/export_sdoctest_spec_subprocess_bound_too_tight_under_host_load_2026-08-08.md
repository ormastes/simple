# `export_sdoctest_spec.spl` subprocess bound: investigated, NOT the actual blocker

**Status:** Closed as not-the-cause — duplicate root cause of
`sdoctest_mode_unknown_extern_rt_string_ends_with_2026-08-07.md`
**Date:** 2026-08-08
**File:** `test/01_unit/app/simple_lab/export_sdoctest_spec.spl:131`

## Original claim

`process_run_bounded("bin/simple", ["test", "--sdoctest", FIXTURE_SDOCTEST_MD],
30000, 65536)` was reported to assert a 30000ms completion bound that is too
tight under host load, with a measured ~78s completion time.

## Investigation (2026-08-08)

Host load at measurement time: `uptime` load average ~5.5 on 32 cores (moderate,
not pegged) — not the "heavy concurrent load" the original report described.

### Standalone baseline (`bin/simple test --sdoctest <fixture>` run directly, x2
measured; a 3rd run was cut off by an unrelated 2-minute shell timeout, not a
hang):

| run | elapsed | exit code |
|-----|---------|-----------|
| 1   | 40.16s  | 1 |
| 2   | 43.79s  | 1 |

Both runs failed with the same error, **not a timeout artifact**:

```
error: semantic: unknown extern function: rt_string_ends_with
```

This is a pre-existing, already-tracked defect:
`doc/08_tracking/bug/sdoctest_mode_unknown_extern_rt_string_ends_with_2026-08-07.md`.
That doc already names this exact spec/example
(`export_sdoctest_spec.spl`'s `"produces output that passes \`simple test
--sdoctest\`"` example) as blocked by the same root cause.

### Full spec run (`SIMPLE_MODULE_LIMIT=4000 bin/simple test
test/01_unit/app/simple_lab/export_sdoctest_spec.spl`)

Total wall time: 61.45s (whole spec file, all 9 examples, includes compiler
startup/lint pass — not just the one subprocess call).

Result: `Results: 9 total, 8 passed, 1 failed`. The single failure is:

```
✗ produces output that passes `simple test --sdoctest`
  expected 1 to equal 0
```

`exit_code == 1` is a **real completed-process exit code**, not a
`process_run_bounded` timeout sentinel — meaning in this run the inner
`bin/simple test --sdoctest` subprocess finished (with a real error) well
inside the current 30000ms bound. This is inconsistent with the standalone
40-44s measurements above, which is expected: standalone `time` invocations
pay cold-process/JIT/disk-cache costs that a subprocess launched from an
already-warm parent process context does not always pay identically run to
run. The bound was not observed to be the active constraint in the run that
produced the current failure.

## Decision: do NOT raise the bound (path b)

Raising `30000` to `~90000` (3x the ~40-44s standalone baseline) would not
turn this spec green: the assertion that fails is `expect(exit_code).to_equal(0)`,
and `exit_code` is `1` because of the unrelated, already-tracked
`rt_string_ends_with` unknown-extern defect in the `--sdoctest` execution
path, not because the process was killed early. Raising the timeout here would
be a no-op change dressed as a perf-bound fix, and per
`.claude/rules/testing.md` a correct-but-failing spec must stay RED with the
real blocker documented — not have an unrelated knob turned to make the diff
look like progress.

**No edit was made to `test/01_unit/app/simple_lab/export_sdoctest_spec.spl`.**
The spec remains RED, correctly, pending a fix to the `rt_string_ends_with`
unknown-extern defect tracked in
`sdoctest_mode_unknown_extern_rt_string_ends_with_2026-08-07.md`.

## Final verification run

```
SIMPLE_MODULE_LIMIT=4000 bin/simple test test/01_unit/app/simple_lab/export_sdoctest_spec.spl
...
Results: 9 total, 8 passed, 1 failed
```

Unchanged from before this investigation — as expected, since no code was
modified.
