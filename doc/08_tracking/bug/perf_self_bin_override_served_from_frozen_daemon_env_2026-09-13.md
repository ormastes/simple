# `SIMPLE_PERF_SELF_BIN` is served from the test daemon's frozen environment

- Status: OPEN (2026-09-13)
- Found by: PERF-7, re-running a perf parity spec against the BASE seed after
  having run it against the CANDIDATE seed.
- Extends `perf_spec_binary_resolution_falls_through_to_deployed_seed_2026-09-13.md`
  (PERF-6), which covered the directory-mode case. This is the single-file case,
  and it is worse: the binary is not merely defaulted, it is silently taken from
  a PREVIOUS run.

## Repro (measured)

Three single-file invocations of the same spec, in order:

```
SIMPLE_PERF_SELF_BIN=<BASE>  bin/simple test test/05_perf/interp/owned_method_call_parity_spec.spl
    -> [perf] binary=<BASE>   outcome=ERROR passed=2 failed=7      (correct)
SIMPLE_PERF_SELF_BIN=<CAND>  bin/simple test ...same spec...
    -> [perf] binary=<CAND>   outcome=OK     passed=10 failed=0    (correct)
SIMPLE_PERF_SELF_BIN=<BASE>  bin/simple test ...same spec...
    -> [perf] binary=<CAND>   outcome=OK     passed=10 failed=0    (WRONG)
```

The third run asked for the base seed and exercised the candidate. Its verdict is
indistinguishable from a genuine result: 10/10 green, no warning, no diagnostic.
The only thing that betrayed it was the `[perf] binary=` line the spec prints —
which exists solely because PERF-6 was bitten by the sibling defect.

## Cause

`test_runner_client.spl` diverts a request past the light daemon whenever the
caller sets one of a closed list of environment overrides — `_has_binary_override()`
(`SIMPLE_TEST_BINARY` and friends), `SIMPLE_COVERAGE`, `SIMPLE_REQUIRE_GPU`, the
`test_env_gate` family. The daemon is a long-lived process whose environment is
frozen at whichever invocation started it, and the v1 request carries a header,
an expiry and a path — **no environment at all**. The file says so itself, at
length, at lines 709-735.

`SIMPLE_PERF_SELF_BIN` is not on that list. It is, however, exactly the same kind
of variable: it names WHICH BINARY THE SPEC EXERCISES. So a daemon-served run
resolves it from the daemon's stale copy. Whether a given run is correct depends
on whether it happened to start the daemon: the first run above did (daemon
absent), the second did (the first daemon had expired), the third did not.

## Fix

Add `SIMPLE_PERF_SELF_BIN` to `_has_binary_override()`'s list, which is the
existing fail-safe divert for precisely this defect class and needs no new
mechanism. The residual gap that list cannot close is already documented there:
a daemon started WITH the variable set keeps serving it to later runs that do not
set it, because the request carries no environment. The real fix remains putting
the caller's environment in the request.

## Meanwhile

Every perf spec that resolves a binary must print `[perf] binary=<path>` as its
first line in every scenario, and any lane comparing two seeds must read that
line rather than trusting the verdict. PERF-7 re-ran its RED leg after confirming
no daemon was live (`ps -eo pid,args | grep light_daemon` empty); its receipt
records both the wrong run and the corrected one rather than only the corrected
one.
