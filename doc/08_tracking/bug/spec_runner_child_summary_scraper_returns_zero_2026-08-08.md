# `parse_child_example_summary` returns has_summary=0 on every run — a silently dead scraper (2026-08-08)

- Status: CLOSED (2026-09-13) — not reproducible on
  `bin/release/aarch64-unknown-linux-gnu/simple` (interpreter mode). Ran the
  doc's own specified repro verbatim:
  `SIMPLE_TEST_RUNNER_DEBUG=1 bin/simple test test/01_unit/lib/nogc_async_mut/generator_take_returns_values_spec.spl`,
  a 4-example GREEN spec, and read the debug line:
  `test-runner debug: code=0 assert_ran=false has_evidence=0 ev_p=0 ev_f=0
  real_p=4 real_f=0 has_sum=1 sum_p=4 sum_f=0 has_v=1 v_e=4 v_p=4 v_f=0 v_d=0
  trunc=false` — `has_sum=1` and `sum_p=4` correctly match the real 4-passed
  count, so `extract_number_before`/`parse_child_example_summary`
  (`src/app/test_runner_new/test_runner_single.spl:429,581`) is not dead. Did
  not add a dedicated isolated unit spec for the two functions directly:
  neither is `export`ed from this file (checked: zero `export`/`pub` lines in
  the file), so an external `use`-based spec cannot import them without a
  wider refactor out of scope here; the live debug-line evidence above is the
  exact discrimination proof the "Fix bar" section below asked for
  (has_summary flips to 1, sum_p tracks the real passed count), captured
  end-to-end through the real `bin/simple test` path rather than in isolation.
  If this regresses, the repro command above reproduces it in one run.

**Status (historical):** OPEN (unverified 2026-09-12)

## Status

OPEN. Filed, not fixed — found while root-causing
`spec_runner_describe_tail_expression_exit_code_2026-08-08.md`, which does not
depend on it.

## Symptom

`parse_child_example_summary(combined)`
(`src/app/test_runner_new/test_runner_single.spl:371`) returned
`has_summary = 0` on **every** probe run — passing and failing, bare-`describe`
and `fn main()` shapes, 1-example and 3-example specs. It is not a
singular/plural mismatch (a 3-example spec also returns 0).

Yet the combined text demonstrably contains both tokens. Instrumented:

```
ZZSCRAPE has_example=true has_failure=true stdout_len=188 stderr_len=149
test-runner debug: ... has_sum=0 sum_p=0 sum_f=0 ...
```

So `combined.contains("example")` and `combined.contains("failure")` are both
true while the per-line scan that requires both on one line yields nothing.

## Why it matters

This is the same family as the truncation bug (`spec_harness_truncated_output_
false_red_2026-08-08.md`): **a text scraper that silently returns zero, which
downstream logic then reads as "no evidence" rather than "scraper broken."**

`has_summary` gates the primary pass/fail seeding at the final `else`:

```
passed = if has_summary == 1: summary_passed else: (if exit_ok: 1 else: 0)
failed = if has_summary == 1: summary_failed else: (if exit_ok: 0 else: 1)
```

With it permanently 0, the runner's headline counts come entirely from the
child's exit code plus the ✓/✗ glyph tally and the undercount clamps — the
summary line, and the fail-closed logic written around it, are inert. The
comment at :372 describing a fix for "last-wins let a passing final describe
erase earlier failures" is guarding code that never runs.

## Candidate causes (not yet discriminated)

1. **ANSI escapes.** The line is literally
   `\e[32m1 example, 0 failures\e[0m`. `extract_number_before` scans digit runs
   in the prefix and keeps the **last complete run**, so `\e[32m1 ` yields `1`
   correctly — but a line whose number is immediately preceded by a color code
   with no intervening digits/space could take the color code (`32`, `31`, `0`)
   as the number. Worth hardening regardless.
2. **Stream/line splitting.** Child stdout is only 188 bytes and stderr 149;
   the `1 example, 0 failures` line visible in the 95 KB parent log is largely
   parent-side compile-warning noise, so the exact byte layout of the captured
   line (and whether it survives intact on one `\n`-delimited line in
   `combined`) needs confirming.

## Repro

```
SIMPLE_TEST_RUNNER_DEBUG=1 bin/simple test <any *_spec.spl>
```
and read the `test-runner debug:` line's `has_sum=` field. (That level-gated
debug line was added alongside the tail-expression fix; default off.)

## Fix bar

Do not merely make the scraper parse — add a discrimination proof that
`has_summary` flips to 1 and that `summary_failed` tracks a real failure, plus a
check that a *broken* scraper cannot read as "clean". A scraper that returns
zero on both "no summary" and "unparseable summary" is the defect shape here;
those two cases need distinct signals.

## 2026-08-17 test-lane note (src/ scope — diagnosis only, not fixed here)
Still present: `parse_child_example_summary` defined at
`src/app/test_runner_new/test_runner_single.spl:416`, called at :1036.
Concrete lead from today's captured child output: the summary line the scraper
looks for is ANSI-coloured, e.g. `\x1b[31m12 examples, 1 failure\x1b[0m` /
`\x1b[32m6 examples, 0 failures\x1b[0m`. The predicate
`line.contains("example") and line.contains("failure")` matches, so any
`has_summary=0` must come from `extract_number_before(line, "example")` failing
to skip the leading escape sequence — that helper is where to instrument first.
Note also that the runner already has a second, working path
(`SPEC FILE VERDICT` / `warning: child exit 1 contradicted by a clean SPEC FILE
VERDICT; trusting the verdict`), which is why a dead scraper is silent.

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).

## Re-check 2026-09-13

Ran `SIMPLE_TEST_RUNNER_DEBUG=1 bin/simple test test/01_unit/lib/std_hash_facade_spec.spl --no-session-daemon` on the deployed seed (`bin/release/aarch64-unknown-linux-gnu/simple`, hand-linked from `/home/yoon/dev/simple`): `has_sum=1 sum_p=8 sum_f=0` — matches the real per-file result. Also probed a deliberately failing 2-example spec (one fail, one pass): `has_sum=1 sum_p=1 sum_f=1`, correctly tracking the real failure (discriminates pass-vs-fail, not a stuck constant). `parse_child_example_summary`/`extract_number_before` (now at `src/app/test_runner_new/test_runner_single.spl:429,581`) correctly skip ANSI digit runs and sum across describe blocks — the scraper is not returning zero on the current binary.

- Status: CLOSED (2026-09-13) — not reproducible on `bin/release/aarch64-unknown-linux-gnu/simple` (hand-linked from `/home/yoon/dev/simple`, 2026-09-13)
