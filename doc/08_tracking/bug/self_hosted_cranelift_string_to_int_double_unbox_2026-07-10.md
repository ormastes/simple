# Self-Hosted Cranelift String Integer Double Unbox

## Status

Open. This blocks trustworthy native 4K/8K exporter measurements.

## Symptom

A Cranelift entry-closure build of
`backend_measurement_software_export.spl` receives `--width 3840 --height 2160
--dpi 300` but reports `480x270` and DPI `37`. Every parsed integer is divided
by eight.

Before `rt_value_as_int` was added to core C, the same path called address zero
inside `_arg_i32`. After adding the ABI helper, the latent double-unbox became
visible.

## Root Cause

`rt_string_to_int` returns a raw `i64` in Rust, core C, and Simple-core. The
generated `_arg_i32` object calls `rt_string_to_int` and then incorrectly calls
`rt_value_as_int`, shifting the already-raw result right by three.

The Rust Cranelift type map did not classify `rt_string_to_int`,
`rt_string_to_int_lenient`, or `rt_string_to_float` return registers. A focused
unit fix now classifies them as native `I64`/`F64`, and its unit test passes.

## Remaining Deployment Blocker

The canonical full bootstrap in dynload mode rebuilt the Rust seed/runtime but
reused stage2/stage3 native caches and ended with:

```text
Pure-Simple dynload build complete; full CLI relink skipped.
```

A fresh exporter built by that stage2 still emitted the double-unbox and
reported `480x270`. The next session must perform the full CLI relink (or fix
cache invalidation so compiler-Rust codegen changes invalidate stage2) before
repeating the full-size measurement. Do not accept scaled-down output as 4K
evidence.

## Passing Focused Evidence

- `build_vreg_types_stamps_string_parse_runtime_reads`: 1 passed, 0 failed.
- `test_core_lane_runtime_required_abi_stdout_stderr_and_values`: 1 passed, 0
  failed, including negative `rt_value_as_int`.
- Full bootstrap stage3 completed successfully before the stale stage2
  end-to-end result was observed.
