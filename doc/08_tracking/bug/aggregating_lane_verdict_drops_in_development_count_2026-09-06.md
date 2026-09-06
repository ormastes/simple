# Aggregating-lane verdict line drops the in-development count, so every neutralised spec reads as a load failure

**Status:** FIXED 2026-09-06
**Component:** `src/app/test_daemon/light_protocol.spl`, `src/app/test_runner_new/test_runner_main.spl`
**Found via:** `scripts/check/check-plan-acceptance-swept.shs`

## Symptom

The pooled plan-acceptance gate (jobs=8, fresh debug seed, `SIMPLE_MCDC_MODE=off`)
completed in **1029s** and reported:

```
FAIL — 36 spec(s) executed, 44 failed to load/run or neutralise cleanly
specs_attempted=36  specs_loaded_and_ran=32  in_development_tagged=36
```

40 of the 44 offenders were `load-failure-neutralised:<spec>`, i.e. **all 36
tagged specs** (15 named + 21 `(no-marker)`), with `N_NEUTR_ASSERT` — specs
neutralised as genuine assertion failures — reported as **zero**. Three shards
had aborted (rc=124/42/3), but offenders appeared in the five that exited
cleanly too, so shard aborts were never the cause.

## Root cause

`ran_verdict_line` computed executed work from passed and failed only:

```
fn ran_verdict_line(path: text, passed: i64, failed: i64) -> text:
    val executed = passed + failed
```

`in_development_adjust` (`test_runner_main.spl`) neutralises a tagged file to
`passed=0, failed=0, skipped=N`. So for every neutralised file the aggregating
(directory) lane printed:

```
SPEC FILE VERDICT: <path> outcome=NOT_RUN declared>=0 executed=0 passed=0 failed=0 dropped=0
```

— byte-identical to a file that never loaded. Any sweep that classifies by
parsing that line must read a correctly-neutralised spec as a load failure.

The runner contradicted itself inside a single output, which is what made the
diagnosis possible:

```
IN-DEVELOPMENT SKIP  office_cli_tui_ui_access_spec.spl (9 expected failure(s))
SPEC FILE VERDICT: office_cli_tui_ui_access_spec.spl outcome=NOT_RUN executed=0
Results: 0 total, 0 passed, 0 failed, 17 skipped
```

9 + 8 = the 17 skips it counted, while both files reported executed=0.

Note the single-file lane was never affected: it reports the failures as real
failures (`executed=12 rc=1`), so a per-spec run and a directory run of the same
file disagreed. Only the directory lane feeds the gate's neutralisation sweep.

## Fix

`in_development` already existed on `TestFileResult`, documented as "distinct
from environment skips", but `in_development_adjust` left it at its 0 default
and the verdict line never carried it.

- `ran_verdict_line` takes `in_development`, counts it toward `executed`, and
  emits `in_development={n}`.
- `in_development_adjust` sets the field instead of leaving it inferred from
  `skipped > 0`.
- the gate classifies on `in_development=`, retaining the old
  `executed>=1 && failed>=1` shape as a legacy branch so an older runner is
  classified rather than blamed.

Environment skips are deliberately **not** counted toward `executed`: folding
them in would turn a file whose examples all skipped for a missing dependency
into `outcome=OK`, which is the greenwash this distinction exists to prevent.

Verified through the real runner on two specs that were offenders:

| | verdict line |
|---|---|
| before | `outcome=NOT_RUN declared>=0 executed=0 passed=0 failed=0` |
| after | `outcome=OK declared>=9 executed=9 passed=0 failed=0 in_development=9` |

## Why the gate's selftest never caught it

14/14 assertions passed throughout, against a reality where 36 of 36
classifications were wrong. The fake runner emitted `failed=1` for a
neutralised file — a shape the real aggregating lane never produces, because
neutralisation is exactly what zeroes `failed`.

Corrected to the real shape. With that one byte changed, the OLD classifier now
FAILS its own selftest reproducing production exactly
(`load-failure-neutralised:wip_failing_spec.spl`, `0 neutralised as genuine
assertion failures`), and passes 14/14 with the fix — a planted control in both
directions.

**A fixture that cannot exhibit the defect is not a test for it.** That is worth
more than this bug: any gate whose fixtures are written from the same mental
model as the code under test will confirm that model rather than reality. Pin
fixture output to the producer's real bytes.

## Supersedes

`sweep_shard_abort_mislabels_survivors_as_load_failures_2026-09-06.md`, whose
"15 real + 21 shard-abort collateral" reading was wrong: 15 + 21 = 36 = every
tagged spec, which is what ruled the shard aborts out.
