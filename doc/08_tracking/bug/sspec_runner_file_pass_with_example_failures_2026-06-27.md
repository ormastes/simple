# SSpec Runner Reports File PASS With Example Failures

Date: 2026-06-27

## Summary

`bin/simple test` can print failing examples inside an SSpec file while still
marking the file as `PASS` and returning exit code `0`.

## Reproduction

```sh
bin/simple test test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl --mode=interpreter
```

Observed output includes:

```text
7 examples, 6 failures
PASS test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl
exit_code=0
```

The failing examples are explicit expectation failures such as:

```text
expected TODO(gui-web-2d-completion): replace with assertions over current Linux Vulkan evidence, strict render-log compare, and RDOC artifact magic to equal evidence-backed
```

## Expected

When any example fails, the file summary should be `Failed: 1`, the file line
should not be `PASS`, and the process exit code should be nonzero.

## Impact

Completion-check SSpecs can look green in shell automation even when the manual
example summary reports failures. Until fixed, scripts that consume this spec
must grep for `examples, 0 failures` or inspect the example failure count
directly instead of trusting only the process exit code.

## Current Workaround

For the GUI/Web/2D completion criteria spec, treat this as passing only when the
output contains:

```text
7 examples, 0 failures
```

The retained 4K/8K performance scenario is currently the only scenario converted
to evidence-backed assertions; the other six scenarios intentionally fail until
their platform evidence exists.
