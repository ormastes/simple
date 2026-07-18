# Engine2D Metal and SIMD CPU Sample

Use this guide when searching for the actual 2D rendering sample that chooses
its backend from CLI args.

## Sample

- `examples/06_io/ui/engine2d_backend_test.spl`

The sample renders a compact 2D scene with a filled rectangle, circle, thick
line, vertical gradient, rounded rectangle, and text. It reads the framebuffer
back and checks exact pixels for each primitive.

## Commands

Run the always-available SIMD CPU lane:

```bash
bin/simple run examples/06_io/ui/engine2d_backend_test.spl --backend=cpu_simd
```

Run strict Metal selection on macOS:

```bash
bin/simple run examples/06_io/ui/engine2d_backend_test.spl --backend=metal
```

Probe the discoverability sweep:

```bash
bin/simple run examples/06_io/ui/engine2d_backend_test.spl --backend=all
```

`cpu_simd` and `simd_cpu` select the SIMD-instrumented CPU Engine2D surface.
The sample fails the SIMD CPU lane if no SIMD span hits are recorded. Metal is
strict: unavailable Metal is reported and skipped rather than silently accepted
as a CPU fallback.

## Verification

- `test/02_integration/rendering/engine2d_backend_spec.spl` covers backend
  selection, SIMD hit evidence, and strict Metal probe behavior.
- `test/02_integration/rendering/metal_engine2d_readback_spec.spl` covers Metal
  framebuffer readback for GPU-backed clear and filled-rectangle kernels.
- `test/05_perf/graphics_2d/metal_readback_proof_spec.spl` covers raw Metal
  compute-buffer download without tolerance.
