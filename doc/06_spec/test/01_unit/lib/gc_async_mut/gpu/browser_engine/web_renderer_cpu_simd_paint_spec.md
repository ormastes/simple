# Web Renderer CPU SIMD Paint Specification

Manual companion for `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl`.

## Scenarios

- CPU-SIMD remains excluded from GPU-offload routing verdicts.
- Solid-only CPU-SIMD readback uses Engine2D fill spans, records positive fill hits, and records no residual copy/alpha hits.
- Text pages use residual CPU-SIMD presentation and stay pixel-identical to the software layout oracle.
- Public `cpu_simd` text renders also stay pixel-identical to the software layout oracle and record residual copy hits.
- Translucent `rgba(...)` composition stays pixel-identical to the software layout oracle while recording fill and residual copy hits.
- CSS opacity composition stays pixel-identical to the software layout oracle while recording fill and residual copy hits.
- `simd_cpu` and `cpu-simd` aliases route through the same residual presentation path.

## Evidence

Run:

```sh
SIMPLE_LIB=src bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl --mode=interpreter --clean
```

Expected: `7 examples, 0 failures`.

The contract intentionally compares CPU-SIMD residual presentation against
`simple_web_layout_render_html_software_pixels(...)` for text, transparency, and
opacity fixtures. This proves the routing change executes Engine2D SIMD spans
without changing color, alpha, or text output.
