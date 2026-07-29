# Engine2D Strict Backend Probe

> Executable source: `test/05_perf/graphics_2d/backend_probe_spec.spl`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 6 | 6 | 0 | 0 |

## Purpose

Verify production backend probing and strict creation without synthetic probe
objects or silent GPU-to-CPU fallback.

## Scenarios

### Portable CPU baseline

The CPU backend must initialize, preserve `cpu` identity, render a red rectangle
over black, and return the expected pixels.

### CUDA

An initialized CUDA probe must preserve CUDA identity and PTX format, then pass
strict creation, dispatch, and readback. An unavailable host must return a
non-empty structured failure and must not select CPU or software.

### Vulkan

An initialized Vulkan probe must preserve Vulkan identity and SPIR-V format,
then pass strict creation, dispatch, and readback. An unavailable host must
return a non-empty structured failure and must not select CPU or software.
The multi-primitive fixture additionally requires full-frame CPU parity, stable
device identity, a positive backend handle, and device readback without the
backend's sticky CPU-fallback provenance.

### Metal

An initialized Metal probe must preserve Metal identity and MSL format, then
pass strict creation, dispatch, and readback. Non-macOS hosts must return a
non-empty structured failure, report the `macos` feature gate, and must not
select CPU or software.

## Run

```bash
bin/simple test test/05_perf/graphics_2d/backend_probe_spec.spl --mode=interpreter --no-session-daemon
```

The legacy mirror at `test/perf/graphics_2d/backend_probe_spec.spl` must remain
byte-identical.
