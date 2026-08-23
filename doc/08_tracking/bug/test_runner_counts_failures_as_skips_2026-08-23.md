# Test runner reports failing examples as SKIPPED as well as failed

**Date:** 2026-08-23
**Status:** OPEN — isolated with a control, not fixed here (execute lane)
**Found by:** the `@tag:in-development` lane, while proving that
in-development work is not absorbed into the `skipped` bucket.

## Symptom

A spec with **N failing examples and zero skips** reports `N skipped`
alongside `N failed`. Measured on an UNTAGGED control fixture with three
deliberately failing examples and no `skip()`/`skip_it()`/`pending()`
anywhere in it:

```
FAIL  test/01_unit/lib/spec/indev_ctl/ctl3_spec.spl (0 passed, 3 failed, 3 skipped, 677ms)
SPEC FILE VERDICT: ctl3_spec.spl outcome=ERROR declared>=3 executed=3 passed=0 failed=3 dropped=0
Results: 3 total, 0 passed, 3 failed, 3 skipped
```

Note the contradiction inside one run: the SPEC FILE VERDICT line — the
authoritative one — says `executed=3 passed=0 failed=3` and mentions no
skips at all, while `Results:` and the per-file line both claim 3 skipped.

## Why it matters

`skipped` is supposed to mean "this environment could not run it" (no GPU,
wrong OS, `@tag:qemu`). Inflating it with ordinary failures makes the skip
count useless as a signal and makes any sweep that reads it over-report
environmental gaps. It also inflates `total_skipped` across a whole run.

## Why it is filed here rather than fixed

It is in the execute lane's result parsing (`run_test_file_interpreter`,
`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:245`
`skipped: result.skipped`), not in the in-development path.

## How it was isolated, and what it is NOT

It surfaced as an apparent in-development defect: a sweep of a tagged
3-failing-example fixture printed `Results: 0 total, 0 passed, 0 failed,
3 skipped`, which looked exactly like in-development being neutralised
INTO the skip bucket — the precise thing that lane had just been told to
stop doing.

Four hypotheses were killed BY MEASUREMENT before the real cause was
found, and they are recorded so nobody re-runs them:

1. **The new `TestFileResult.in_development` field is landing in
   `skipped`** (struct/default mis-assignment). Killed by a direct probe:
   `skipped=0 in_development=1 passed=0 failed=0`. Fields assign
   correctly.
2. **A second neutralisation write site still assigns `skipped:
   expected`.** Killed by grep: exactly one write site exists, and it
   reads `skipped: raw.skipped`.
3. **The printer displays in-development under a "skipped" label.**
   Killed by reading `print_result_default`
   (`test_runner_output.spl:86-87`), which reads `result.skipped` plainly.
4. **A stale/duplicate copy of the runner was executing.** Killed by the
   fact that the run printed markers that exist only in the new source.

The decisive experiment was the UNTAGGED control above: same shape, no
tag, still `3 skipped`. So the count was never written by the
in-development path — it arrives from the execute lane already wrong, and
in-development merely propagates it faithfully.

**Method note worth keeping:** the tagged fixture alone could not
distinguish the two explanations, because the neutralised count and the
bogus skip count were both 3. Varying the example count (1 -> 3) and then
dropping the tag is what separated them.

## Repro

```bash
mkdir -p test/01_unit/lib/spec/indev_ctl
cat > test/01_unit/lib/spec/indev_ctl/ctl3_spec.spl <<'SPEC'
use std.spec.{step}
describe "ctl three":
    it "f1":
        step("a")
        expect(1).to_equal(2)
    it "f2":
        step("a")
        expect(1).to_equal(3)
    it "f3":
        step("a")
        expect(1).to_equal(4)
SPEC
bin/simple test test/01_unit/lib/spec/indev_ctl
```

Expected: `3 total, 0 passed, 3 failed` and **0 skipped**.
Actual: `3 total, 0 passed, 3 failed, 3 skipped`.

## Suggested fix

Trust the SPEC FILE VERDICT line's accounting, or derive `skipped` only
from real skip markers (`count_real_skips` already does exactly this in
`test_runner_single.spl:441` for the single-file lane) rather than from
whatever the aggregate parse currently infers. The single-file lane and
the aggregate lane disagreeing about the same file is itself the bug
signature.
