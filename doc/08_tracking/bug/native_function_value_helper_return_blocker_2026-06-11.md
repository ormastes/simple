# Native Function Value Helper Return Runtime Regression

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

The helper-returned function-value boundary is now fixed in current source:

- the native symbol-collision sub-bug (`undefined symbol: worker.1`) remains
  fixed
- current-source rebuilt release and debug binaries compile the helper probes
  to standalone native artifacts
- those rebuilt binaries now preserve and invoke helper-returned function
  values correctly

The remaining hosted multicore-green resumable-stepper crash is a separate
downstream blocker.

## Minimal Contrast

Previously failing compile-time release sub-boundary, now fixed:

```text
Compiled /tmp/helper_return_value_only_probe.spl -> ...release_after.bin
Compiled /tmp/helper_return_fn_value_probe.spl -> ...release_after.bin
```

Current passing rebuilt native probes:

- same global function array
- helper returns the function value:
  - `fn get0() -> fn() -> i64: FUNCS[0]`
- observed:

```text
value-only: EXIT=7
helper-call: direct=7
helper-call: via_helper=7
helper-call: EXIT=0
```

## Why This Matters

The earlier resumable-stepper blocker was narrowed correctly to this lower
boundary first, and this fix closes that lower boundary. The resumable-stepper
lane still crashes, so it now needs investigation as its own native runtime
problem rather than as a helper-returned function-value misroute.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_helper_return_regression_spec.spl`
