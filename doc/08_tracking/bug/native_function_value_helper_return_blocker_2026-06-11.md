# Native Function Value Helper Return Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The hosted native callback boundary under the multicore-green resumable-stepper
experiment is narrower than “function values are broken”:

- direct global-array callback native path still works
- returning the function value from a helper still segfaults

That is the next concrete native compiler/runtime blocker for any callback-id
resumable scheduler layered over the current hosted worker pool.

## Minimal Contrast

Working hosted native probe:

- global `var FUNCS: [fn() -> i64]`
- `FUNCS.push(worker)`
- direct call: `FUNCS[0]()`
- observed:

```text
got=<value:0x7>
EXIT=0
```

Failing hosted native probe:

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

The earlier resumable-stepper blocker is downstream of this lower boundary.
That experiment used callback-id lookup plus helper-returned function values
before invoking the next step. Until helper-returned function values are stable
on the hosted native path, the explicit resumable fairness lane cannot move
forward honestly.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_helper_return_blocker_spec.spl`
