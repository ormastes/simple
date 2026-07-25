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

Before the fix, completion-check SSpecs could look green in shell automation
even when the manual example summary reported failures.

## Historical Workaround

Before `test_runner_single.spl` parsed child example summaries directly, the
GUI/Web/2D completion criteria spec had to be treated as passing only when the
output contained:

```text
7 examples, 0 failures
```

Automation can also run:

```sh
scripts/check/check-gui-web-2d-completion-criteria-placeholders.shs
```

That check fails while any `TODO(gui-web-2d-completion)` placeholder remains in
the executable completion criteria spec and emits
`gui_web_2d_completion_criteria_todo_count` evidence. Use
`GUI_WEB_2D_COMPLETION_ALLOW_INCOMPLETE=1` only for status dashboards that need
to record the current incomplete count without failing the shell command.

The retained 4K/8K performance scenario is currently the only scenario converted
to evidence-backed assertions; the other six scenarios intentionally fail until
their platform evidence exists.

## Fix

The minimal child runner `src/app/test_runner_new/test_runner_single.spl` now
parses child output lines such as `N examples, M failures` before printing its
own file summary. If the child reports any example failures, the wrapper prints
`FAIL` and returns nonzero even when the child process itself exits `0`.

Regression coverage:

```sh
bin/simple test test/03_system/check/test_runner_single_example_failure_contract_spec.spl --mode=interpreter
```
