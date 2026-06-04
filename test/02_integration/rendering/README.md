# test/integration/rendering

Integration specs for the Engine2D rendering backends.

## Running the Tests

Run all rendering specs:

```
bin/simple test test/integration/rendering/
```

Run only the backend matrix or perf smoke:

```
bin/simple test test/integration/rendering/backend_matrix_spec.spl
bin/simple test test/integration/rendering/perf_smoke_spec.spl
```

## Test Files Added by Agent H

| File | Purpose |
|------|---------|
| `backend_matrix_spec.spl` | Forced-backend probe matrix — every known backend, classified by result |
| `perf_smoke_spec.spl` | Per-backend timing fields (init, clear, dispatch, present, readback, RSS) |

## Result Classification

`backend_matrix_spec.spl` classifies each `create_with_backend_strict()` call as one of:

| Label | Meaning |
|-------|---------|
| `HARDWARE_PASS` | Init succeeded; `is_hardware()` is true (real GPU device) |
| `SOFTWARE_PASS` | Init succeeded; device is a software or cpu renderer |
| `UNAVAILABLE` | `BackendStatus.Unavailable` — feature gate missing or no driver found |
| `FAILED` | `BackendStatus.Failed` — driver present but init error |

CPU backend is the only backend with a hard `PASS` assertion. All other backends
may be `UNAVAILABLE` on any given host.

## Environment Gates

Set these env vars to require specific backends to be `HARDWARE_PASS`.
Absent any gate, hardware-backend tests always green-pass regardless of the
probe outcome.

| Env var | Effect |
|---------|--------|
| `FORCE_CUDA=1` | Fail if cuda is not `HARDWARE_PASS` |
| `FORCE_VULKAN=1` | Fail if vulkan is not `HARDWARE_PASS` |
| `FORCE_METAL=1` | Fail if metal is not `HARDWARE_PASS` |
| `FORCE_ROCM=1` | Fail if rocm is not `HARDWARE_PASS` |
| `FORCE_WEBGPU=1` | Fail if webgpu is not `HARDWARE_PASS` |
| `FORCE_OPENGL=1` | Fail if opengl is not `HARDWARE_PASS` |

These gates are enforced by CI job configuration, not by the spec itself. The
spec always reports its classification via `print`; the CI wrapper can grep for
`[HARDWARE_PASS]` on the required backend.

## CI Matrix

CPU-only path: runs on every PR. The `cpu` backend always passes.

Hardware-specific jobs are opt-in CI jobs with the corresponding `FORCE_*=1`
env var set. Example GitHub Actions matrix entry:

```yaml
- name: vulkan-gpu
  env:
    FORCE_VULKAN: "1"
  run: bin/simple test test/integration/rendering/backend_matrix_spec.spl
```

## Perf Smoke Fields

`perf_smoke_spec.spl` measures and prints:

```
PERF backend=cpu init_ms=0 clear_ms=0 dispatch_ms=0 present_ms=0 readback_ms=0 rss_kb=14208
```

| Field | Units | Notes |
|-------|-------|-------|
| `init_ms` | ms | `create_with_backend_strict()` call time |
| `clear_ms` | ms | `engine.clear()` call time |
| `dispatch_ms` | ms | `engine.draw_rect_filled()` call time |
| `present_ms` | ms | `engine.present()` call time |
| `readback_ms` | ms | `engine.read_pixels()` call time |
| `rss_kb` | KB | Process RSS after init; -1 if `rt_process_rss()` is not available |

Timing is measured via `std.src.time.now_micros()` and divided by 1000 for ms.
No absolute thresholds are enforced — the fields are informational and intended
for tracking regressions over time in CI artifacts.
