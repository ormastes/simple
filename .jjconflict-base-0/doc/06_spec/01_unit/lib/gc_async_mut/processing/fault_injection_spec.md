# ProcessingIR Fault Injection Spec

## Purpose

Verify the disabled-default fault gate and the one-match delay used by the
native daemon fallback harness.

## Run

```sh
SIMPLE_LIB=src bin/simple test \
  test/01_unit/lib/gc_async_mut/processing/fault_injection_spec.spl \
  --mode=interpreter
```

## Checks

1. No fault is injected without `SIMPLE_GPU_TEST=1`.
2. A different phase does not consume the skip counter.
3. With `SIMPLE_GPU_FAULT_INJECT_SKIP_MATCHES=1`, the first exact match is
   skipped and the second exact match is injected.
4. Changing the selected backend/phase resets the one-match delay.
