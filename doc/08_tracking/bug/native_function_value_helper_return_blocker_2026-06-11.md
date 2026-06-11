# Native Function Value Helper Return Debug Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The current callback boundary under the multicore-green resumable-stepper
experiment is narrower than “function values are broken” and narrower than the
earlier generic hosted-native claim:

- the checked-in `bin/release/simple` path now handles helper-returned function
  values in standalone native binaries
- the fresh debug seed binary still segfaults when a helper returns a function
  value and the caller invokes it in the standalone native artifact

That leaves a smaller debug-seed blocker under the callback-id resumable
scheduler experiment layered over the current hosted worker pool.

## Minimal Contrast

Working release native probe:

- global `var FUNCS: [fn() -> i64]`
- `FUNCS.push(worker)`
- helper-returned call: `get0()()`
- observed:

```text
direct=7
via_helper=7
EXIT=0
```

Failing debug-seed native probe:

- same global function array
- helper returns the function value:
  - `fn get0() -> fn() -> i64: FUNCS[0]`
- indirect call:
  - `get0()()`
- observed:

```text
Segmentation fault (core dumped)
EXIT=139
```

## Why This Matters

The earlier resumable-stepper blocker is downstream of this lower boundary on
the debug-seed path. That experiment used callback-id lookup plus
helper-returned function values before invoking the next step. The checked-in
release path no longer blocks there, but the fresh debug seed binary still does.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_helper_return_blocker_spec.spl`
