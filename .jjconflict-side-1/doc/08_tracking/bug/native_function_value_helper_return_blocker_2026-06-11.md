# Native Function Value Helper Return Regression

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

The helper-returned function-value boundary is now closed on the fresh native
debug path that drives the multicore-green hosted parity lane.

- current-source rebuilt debug binaries compile both helper probes to standalone
  native artifacts
- the scalar helper-return probe now prints `got=7`
- the object-return helper probe now prints `done=true` and `value=7`
- both native binaries exit `0`

The remaining hosted parity blocker is no longer helper-returned function
values. The resumable-stepper native crash remains a separate blocker.

## Minimal Contrast

Current passing native probes:

```text
scalar helper: got=7
scalar helper: EXIT=0
object helper: done=true
object helper: value=7
object helper: EXIT=0
```

The fix combined two seed-side corrections:

- `compilability.rs` no longer forces interpreter fallback for plain index
  expressions
- HIR lowering now keeps bare callable identifiers in value position typed as
  function values instead of collapsing them to their return type

## Why This Matters

The earlier resumable-stepper blocker was partially downstream of this lower
boundary. That dependency is now removed, which means the remaining
resumable-stepper crash is a more trustworthy standalone host-fairness blocker.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_helper_return_regression_spec.spl`
