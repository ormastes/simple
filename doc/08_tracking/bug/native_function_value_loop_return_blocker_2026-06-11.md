# Native Function Value Loop Return Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The current lower native blocker beneath the hosted `multicore_green`
resumable-stepper fairness experiment is narrower than the stepper itself:

- returning a function value from inside a loop/search branch still crashes in
  standalone native artifacts
- the failure reproduces with a plain named `fn() -> i64`
- no worker pool, channels, callback-id queueing, or struct-return payload is
  required to trigger it

That means the resumable-stepper native crash is currently downstream of a more
basic native function-value control-flow bug.

## Minimal Boundary

Current minimal probe:

- `var IDS: [i64]`
- `var FUNCS: [fn() -> i64]`
- helper:
  - scans `IDS` with `for i in 0..IDS.len()`
  - on match, `return FUNCS[i]`
- caller invokes `get_func(1)()`

Observed behavior:

```text
source-run: passes
native compile: passes
native run: EXIT=139
```

## Why This Matters

The hosted fairness lane should not blame `multicore_green` first when a
smaller standalone native function-value control-flow path is already broken.

Until this lower bug is fixed:

- the callback-id resumable-stepper experiment cannot prove much about hosted
  fairness on its own
- the remaining host-side Go-like M:N gap is partially blocked by native
  function-value return/control-flow correctness

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_loop_return_blocker_spec.spl`
