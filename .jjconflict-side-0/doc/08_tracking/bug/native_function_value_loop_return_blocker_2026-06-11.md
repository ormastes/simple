# Native Function Value Loop Return Blocker

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

The lower native blocker that previously sat beneath the hosted
`multicore_green` resumable-stepper fairness experiment is now closed:

- returning a function value from inside a loop/search branch now works in
  standalone native artifacts
- the fix holds for a plain named `fn() -> i64`
- no worker pool, channels, callback-id queueing, or struct-return payload is
  required for the positive regression probe

That means the resumable-stepper native crash remains downstream of this path,
but this lower standalone-native function-value control-flow bug is no longer
the active blocker.

## Minimal Boundary

Current minimal probe:

- `var IDS: [i64]`
- `var FUNCS: [fn() -> i64]`
- helper:
  - scans `IDS` with `for i in 0..IDS.len()`
  - on match, `return FUNCS[i]`
- caller invokes `get_func(1)()`

Current observed behavior:

```text
source-run: passes
native compile: passes
native run: EXIT=0
```

## Why This Matters

This regression matters because it removes a false lower bound from the hosted
fairness lane.

With this lower bug closed:

- the callback-id resumable-stepper experiment is again the narrower active
  native blocker under hosted fairness work
- the remaining host-side Go-like M:N gap is no longer explained by this plain
  function-value return/control-flow path

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_loop_return_regression_spec.spl`
