# Test runner (interpreter mode): file summary reports Failed: 0 despite failing examples

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

- **Date:** 2026-07-03
- **Severity:** P1 (trust — CI/agents reading the summary see green on red)
- **Repro:** run a spec whose `it` blocks fail under `--mode=interpreter`, e.g.
  (before its fix) `bin/simple test examples/12_business/simple_erp/ubs_test/durable_log_spec.spl --mode=interpreter`
  from a cwd without a `build/` directory.

## Observed

Per-describe output correctly prints red ✗ marks and e.g. "2 examples, 2
failures", but the end-of-run file summary prints `Passed: N / Failed: 0`,
the file line prints `PASS`, and the process exits 0.

## Expected

Any failing example must fail the file: summary `Failed: >0`, `FAIL` line,
non-zero exit. The documented interpreter-mode limitation ("runner only
verifies file loading") should not apply here — the examples DID run and DID
report failures; only the aggregation drops them.

## Impact

Automated verification that greps `^PASS` or trusts the exit code reports
green on genuinely red specs. Workaround until fixed: also grep the per-block
output for `✗` / `[1-9][0-9]* failures?`.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
