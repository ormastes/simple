# Test runner (interpreter mode): file summary reports Failed: 0 despite failing examples

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
