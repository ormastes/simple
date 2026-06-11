# Native Function Value Helper Return Runtime Blocker

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

The current callback boundary under the multicore-green resumable-stepper
experiment is narrower than “function values are broken” and narrower than the
earlier generic hosted-native claim:

- the native symbol-collision sub-bug (`undefined symbol: worker.1`) is now
  fixed in current-source rebuilt release/debug compilers
- current-source rebuilt release and debug binaries now both compile the helper
  probes to standalone native artifacts
- those same rebuilt binaries still lose the returned function value at runtime:
  - value-only helper probe prints raw nil tag `3`
  - helper-returned indirect call still segfaults with `EXIT=139`

That leaves a smaller runtime/value-shape blocker under the callback-id
resumable scheduler experiment layered over the current hosted worker pool.

## Minimal Contrast

Previously failing compile-time release sub-boundary, now fixed:

```text
Compiled /tmp/helper_return_value_only_probe.spl -> ...release_after.bin
Compiled /tmp/helper_return_fn_value_probe.spl -> ...release_after.bin
```

Current failing rebuilt native probes:

- same global function array
- helper returns the function value:
  - `fn get0() -> fn() -> i64: FUNCS[0]`
- observed:

```text
value-only: f=3
helper-call: direct=7
helper-call: Segmentation fault (core dumped)
helper-call: EXIT=139
```

## Why This Matters

The earlier resumable-stepper blocker is downstream of this lower boundary on
both rebuilt release and rebuilt debug seed paths. That experiment used
callback-id lookup plus helper-returned function values before invoking the
next step. The symbol-collision layer is gone; the remaining blocker is the
returned function value itself collapsing to nil / crashing when invoked.

## Executable Evidence

- `test/03_system/feature/usage/native_function_value_helper_return_blocker_spec.spl`
