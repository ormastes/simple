# `exp` app CLI: experiment script execution falls back to usage/help text instead of delegating

**Date:** 2026-07-20
**Component:** `src/app/exp/main.spl` CLI script-delegation path
**Severity:** Low-Medium — single isolated example; 4 of 5 examples in the
spec file pass
**Found by:** whole-suite triage campaign,
`test/02_integration/app/exp_log_modes_spec.spl`

## Symptom

```simple
it "delegates experiment script execution":
    val (out, err, code) = _run_exp_temp_script()
    expect(code).to_equal(0)
    expect(out).to_contain("exp-run-ok")
```

fails: expected `out` to contain the marker `exp-run-ok` (which the target
temp script presumably prints when actually executed), but actual output
starts with the CLI's own usage banner (`usage: 0/1 (0%)\nexp - Experiment
Tracking CLI...`) — i.e. the `exp` CLI printed its help/usage text instead
of delegating to and running the temp script.

## Root-cause hypothesis

Not root-caused to the exact dispatch code in `src/app/exp/main.spl`
(time-boxed triage). Looks like whatever argument shape `_run_exp_temp_script()`
constructs (helper not inspected in depth here) isn't being recognized by
the CLI's script-delegation branch, so it falls through to the default
usage-printing path — consistent with either an arg-parsing gap or the
delegation subcommand having a different expected invocation shape than the
test provides.

## Note

Spec left unmodified — could not confirm from source whether the test's
invocation shape or the CLI's dispatch is out of sync; flagging as a
genuine gap.
