# Spec harness reports two contradictory verdicts: truncated child output false-RED

- **Date:** 2026-08-08
- **Status:** FIXED (pure-Simple, `src/app/test_runner_new/test_runner_single.spl`)
- **Severity:** High — a genuinely passing spec reported `exit 1` / `0 passed, 1 failed`

## Symptom

One `bin/simple test <spec>` run printed BOTH of these:

```
SPEC FILE VERDICT: <path> declared>=1 executed=1 passed=1 failed=0 dropped=0
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed        # process exits 1
```

## Which surface was lying

**`SPEC FILE VERDICT` was TRUTHFUL. `Results:` and the exit code were the FALSE RED.**

Established independently of both reported numbers: the `it` body wrote a
sentinel FILE (`rt_file_write_text`) before asserting. The file was present with
`IT_BODY_RAN_AND_ASSERTION_PASSED` on every failing run. A file write cannot be
lost to stdout capture, so the example demonstrably executed and passed while the
runner called the file failed.

This is a false RED, not a greenwash — the less dangerous polarity. No past
"green" result is retroactively suspect from this defect; some past **RED**s in
high-output specs may have been spurious.

## IMPORTANT: this is A mechanism, not necessarily THE reported one

The original report described the contradiction coming from a **one-line
trivially-passing spec under `src/lib/**/test/`**. That exact experiment was run
here (`src/lib/common/test/zprobe_ctl_spec.spl`) and came back **green and
self-consistent**. So the finder's case was *not* reproduced.

What was found is a distinct, fully-proven mechanism producing the **identical
signature**. It cannot be the finder's case as literally described, because it
requires >4 MB of child stdout and a one-line spec's full run log measured only
**81 KB** here — two orders of magnitude short. (The "child lint noise pushes it
over the cap" theory was tested and is FALSE at that size.)

Therefore: **the finder's `src/lib/**/test/` one-liner case remains
unexplained and OPEN.** It is a second mechanism. Do not read this record as
having characterized it. What the axis controls below do establish is that
directory, entry shape, imports, example count and `--assert-ran` do not *by
themselves* trigger the contradiction on a quiet run.

## Trigger condition (precise) — for the mechanism fixed here

Not directory shape, not entry shape, not imports, not example count — each was
held constant against the other (`src/lib/**/test/` vs `test/01_unit/...`,
top-level `describe` vs `fn main(): describe`, with/without imports, nested
describes, multiple examples, `--assert-ran`) and every one of those runs was
consistent and green.

The trigger for THIS defect is **child stdout volume**:

1. the spec's child process emits **more than 4 MB** on stdout
   (`TEST_OUTPUT_CAPTURE_BYTES = 4 * 1024 * 1024`,
   `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:5`), **and**
2. more than 2 MB of it precedes the first example, **and**
3. more than 2 MB of it follows the last per-describe summary line.

## Root cause

`spawn_bounded_output_reader`
(`src/compiler_rust/runtime/src/value/sffi/env_process.rs:362-410`) is a
**head+tail** reader: it retains the first `max/2` and last `max/2` bytes and
**discards the MIDDLE**, splicing in `[output truncated: N bytes omitted]`.

The driver's `SPEC FILE VERDICT` line is emitted **last**
(`report_spec_file_verdict`, `src/compiler_rust/driver/src/cli/basic.rs:169`), so
it always survives in the retained tail. But the per-example `✓`/`✗` glyphs
(`interpreter_call/bdd.rs:734,757,763`) and the per-describe
`N examples, M failures` lines sit in the middle and are deleted.

`test_runner_single.spl` then scrapes that mutilated text:
`count_real_examples` (line ~291) returns `(0,0)` and
`parse_child_example_summary` (line ~306) returns `has_summary = 0`. The
fail-closed zero-executed guard fires and sets `failed = 1, passed = 0` —
fail-closing on evidence that was merely **deleted**, not absent. The
authoritative verdict line was sitting in the same buffer, unparsed, saying
`executed=1 passed=1 failed=0`.

The truncation marker was already being emitted by the runtime and was ignored by
every consumer.

## Fix

`src/app/test_runner_new/test_runner_single.spl`, pure-Simple only (no seed
change, no rebuild):

- `parse_spec_file_verdict(output)` — parses the authoritative
  `SPEC FILE VERDICT:` line into `(executed, passed, failed, has_verdict)`.
  Its counts come from the interpreter's own BDD result table rather than from
  display text, so it is strictly more reliable than glyph/summary scraping.
- `output_was_truncated(output)` — detects `[output truncated:`.
- `extract_number_after(s, keyword)` — `key=<n>` field reader.
- A new branch ahead of the zero-executed guard, gated on **all** of:
  truncation marker present **and** `has_verdict == 1` **and**
  `verdict_executed > 0` **and** both scraped signals empty. It then trusts the
  verdict line's pass/fail counts.

This does **not** weaken the existing zero-executed greenwash guard
(`test_runner_zero_executed_single_file_greenwash_2026-07-17.md`): absent the
truncation marker, behaviour is byte-identical to before. The pending()-only
greenwash case is additionally excluded by `verdict_executed > 0`.

## Controls (all four directions)

| case | output | expected | got |
|---|---|---|---|
| passing spec, truncated | >4MB, middle dropped | PASS / exit 0 | PASS, `1 total, 1 passed, 0 failed`, exit 0 |
| failing spec, truncated | >4MB, middle dropped | FAIL / exit 1 | FAIL, `1 total, 0 passed, 1 failed`, exit 1 |
| passing spec, normal | fits in cap | PASS / exit 0 | PASS, exit 0 |
| failing spec, normal | fits in cap | FAIL / exit 1 | FAIL, exit 1 |

Ground-truth sentinel file agreed with the reported verdict in all four.

**SABOTAGE:** reverting `test_runner_single.spl` to the `origin/main` version and
re-running the same repro reproduced the contradiction exactly
(`VERDICT ... passed=1 failed=0` + `error: test-runner: no examples executed` +
`Results: 1 total, 0 passed, 1 failed`, exit 1) while the sentinel file still
said the example ran and passed. Restoring the fix returned exit 0. Same binary,
same spec — this also positively proves the `.spl` edit is live on the
`bin/simple test` interpreter path.

## Blast radius

Structural, not directory-based: any spec whose child emits >4 MB on stdout with
material output on both sides of its examples. The corpus is 24,925 specs under
`test/` plus 183 under `src/lib/**/test/`, but only high-output specs can trip
it, and the failure direction is RED — so this recalibrates **spurious failures**,
never past greens. `doc/08_tracking/test/test_result.md` currently records 0
occurrences of `no examples executed`.

## Lane coverage

`test_runner_single.spl` is the per-file execution lane that BOTH suite paths
spawn once per spec (`test_runner_client.spl:231`, `test_daemon/light_daemon.spl:102`),
so the fix applies to directory/suite runs too, not just explicit single-file
invocations. The aggregators above it scrape the child's `Results:` / `PASS` /
`FAIL` lines, which are emitted last and therefore survive in the retained tail
of their own bounded capture.

## Follow-up (not done here)

**OPEN: the finder's one-line `src/lib/**/test/` case is still unexplained** (see
the section at the top). A second mechanism with the same signature exists and
was not isolated. Anyone reproducing it should grep their log for the four
branch-identifying strings, which name the branch uniquely:
`error: test-runner: file timed out` (line ~849, child killed),
`error: test-runner: spec failed` (~858, non-zero exit under `--assert-ran`),
`error: --assert-ran: no BDD examples executed` (~862, missing evidence file),
`error: test-runner: no examples executed` (~871, the one fixed here).



Other consumers of `process_run_bounded` scrape the same head+tail-truncated text
and none of them check the truncation marker either:
`src/app/test_runner_new/test_runner_main.spl:101`,
`test_runner_client.spl:245`, `src/app/test_daemon/light_daemon.spl:104`,
`src/lib/nogc_sync_mut/test_runner/sdoctest/runner.spl:324`, and the parallel
parsing copy in
`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`. The
directory/multi-file aggregation lanes should get the same verdict-line
preference; only the single-file lane is fixed here.
