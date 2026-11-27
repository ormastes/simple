# `ctx_capture_truncation_spec` fails 2 of 4 on Windows: an over-cap capture comes back as WallTimeout with 0 bytes

Date: 2026-11-15
Status: OPEN (filed, not fixed; root cause only probable)
Area: `test/01_unit/app/mcp/ctx_capture_truncation_spec.spl`, `src/app/mcp/main_lazy_ctx_tools.spl`, `src/lib/nogc_sync_mut/io/resource_scope.spl`

## Symptom

`bin/simple.exe test test/01_unit/app/mcp/ctx_capture_truncation_spec.spl`
(release/1.0.0 base 2cf3dc7e5ec, run twice, identical):

```
SPEC FILE VERDICT: ... outcome=ERROR declared>=4 executed=4 passed=2 failed=2
Results: 4 total, 2 passed, 2 failed
```

Failing cases (the two that produce 20000 bytes with a smaller cap):

1. `marks and counts a capture that hits capture_bytes` - command
   `yes abcdefgh | head -c 20000`, capture_bytes 1024. Batch line was
   `[0] TIMEOUT, 0 stdout byte(s), 1 chunk(s) -> source trunc:cap#0`;
   `assert_contains ... '[capture truncated at 1024 bytes]'` failed, then
   `assert_equal failed: expected 1, got 0` (capture_truncations).
2. `detects the cap from the runtime marker when the receipt flag is dropped` -
   `ctx_run_bounded(sh, args, 15000, 512)`: `assert_true(res.truncated)` got
   false; `assert_equal(_truncations(), 1)` got 0.

Passing: "does not mark or count a capture under the cap", "does not treat
unrelated text mentioning both marker fragments as truncated" (both small output).

## Findings

- Two candidate causes were separated by experiment. In this host's Git Bash
  `yes zzzzzzzz | head -c 20000 | wc -c` took ~10 s once and a later run had
  not returned after 120 s (yes is not reaped after head exits). Replacing the
  generator with the terminating `head -c 20000 /dev/zero | tr -c a a`
  (0.7 s in Git Bash, 20000 bytes) in both cases did NOT change the result:
  the spec still reported `Results: 4 total, 2 passed, 2 failed` with the same
  `[0] TIMEOUT, 0 stdout byte(s)` line. So the `yes` pipe is a hazard but is
  not the cause; that edit was reverted.
- Probable cause (not proven): on Windows `process_run_observed_bounded`
  (`src/lib/nogc_sync_mut/io/resource_scope.spl:687-688`) routes to
  `_legacy_process_fallback` (`:628`) -> `process_run_bounded`. The path
  classifies timeout via `process_bounded_timed_out(exit, stderr)` (`:633`),
  and `ctx_run_bounded` (`src/app/mcp/main_lazy_ctx_tools.spl:872`) turns that
  into `timed_out`. A command whose output exceeds the cap appears to be
  reported as a wall timeout with an empty stream, so `p.stdout_truncated`
  (`:874`) is false and `_ctx_stats_bump("capture_truncations", 1)` (`:885`)
  never runs. The runtime that owns the over-cap behaviour on this seed is
  the `rt_process_run_bounded` implementation (`runtime_process.c`
  `win_capture_finish`, or the seed's `interpreter_extern/system.rs`), which
  was not instrumented here.
- The spec itself comments that on Windows a literal `/bin/sh` does not spawn;
  this is a Windows-seed-specific gap, not a regression in the length-vs-cap
  comparison at `resource_scope.spl:672`.

## Binary identity

`bin/simple.exe --version`: "WARNING: this Rust-built Simple binary is a
bootstrap seed only..." ; 37622272 bytes, mtime 2026-11-15 12:24:16 +0900.

## Unblock condition

Run `ctx_run_bounded` with a >cap producer on the seed and print
`p.usage.termination`, `p.stdout.len()`, and the raw `process_run_bounded`
tuple; fix whichever of the Windows bounded-run implementations misreports
a cap hit as WallTimeout/empty, then this spec goes green unchanged.
