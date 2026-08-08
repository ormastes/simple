# Parallel test timeout classification

**Status:** SOURCE FIXED; RUNTIME QUALIFICATION PENDING
**Severity:** P1 — timeout totals and the stable run outcome could report a killed child as an ordinary failure

## Reproduction

`run_tests_parallel_with_monitoring` passed the pending sentinel `-2` to
`collect_async_result` after the deadline. The tracked wait killed the child and
returned `-1`, but the output mapper recognized a timeout only when stderr also
contained timeout text. A normally killed child therefore produced
`timed_out: false`, and `total_timed_out` remained zero.

## Root fix

The monitor now polls first so a completed child wins at the deadline. Only a
still-pending child past its budget carries an explicit `deadline_expired`
state into collection. Collection still kills/untracks the child and cleans its
bounded capture files, then returns a failed timeout result without treating
ordinary `-1` crash/start failures as timeouts.

Regression: `test/01_unit/app/test_runner_parallel_timeout_contract_spec.spl`
uses no sleep or child process and proves explicit deadline classification plus
capture cleanup.

## Evidence boundary

High-capability source review passed. The deployed pure-Simple wrapper returned
zero with no output for the focused `--assert-ran` command, which is not valid
test evidence. The Rust-seed direct contract then remained live for more than
50 seconds and was terminated by exact process group. Do not claim runtime or
Stage 4 qualification until an admitted pure-Simple runner executes the focused
contract with structured nonempty evidence.
