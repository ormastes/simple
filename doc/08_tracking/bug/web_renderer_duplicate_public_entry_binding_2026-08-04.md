# `simple_web_render_html_to_pixels_with_engine2d_backend` is declared twice; `use` binds to the other module

- **Status:** open
- **Filed:** 2026-08-04
- **Component:** `src/lib/gc_async_mut/gpu/browser_engine/`
- **Severity:** high — it makes sabotage-verification of any spec importing this
  symbol fail-open, and it silently decides which of two different renderers runs.

## The defect

Two modules each export a `pub fn` with the *same name* and the *same signature*
but **different bodies**:

| declaration | body |
|---|---|
| `simple_web_renderer.spl:98` | `_render_engine2d_surface_pixels(html, w, h, _resolved_backend_name(w, h, backend_name))` |
| `simple_web_engine2d_renderer.spl:1170` | `simple_web_engine2d_render_html_pixels(html, w, h, backend_name)` |

A spec that writes

```
use std.gc_async_mut.gpu.browser_engine.simple_web_renderer.{simple_web_render_html_to_pixels_with_engine2d_backend}
```

does **not** get `simple_web_renderer`'s definition. It gets
`simple_web_engine2d_renderer`'s.

Note the two bodies differ in more than routing: only the `simple_web_renderer`
one passes the backend name through `_resolved_backend_name(...)`, so the two
also disagree about backend resolution.

## Evidence (BINDMARK probe, 2026-08-04)

A `print` marker was inserted at the top of *each* of the two bodies and a probe
calling the imported name four times was run:

```
BINDMARK=simple_web_renderer            -> 0 hits
BINDMARK=simple_web_engine2d_renderer   -> 4 hits
```

All four calls reached the `simple_web_engine2d_renderer` definition. The import
naming `simple_web_renderer` had no effect on which body ran.

## Why it matters

This is a **fail-open trap for sabotage verification**. A previous attempt to
prove a spec's assertion could bite perturbed `simple_web_renderer.spl` — the
module actually named in the `use` — and the spec stayed green, because that code
never executes for these callers. The perturbation was a no-op and the green was
meaningless.

The compiler already emits this class of warning for other symbols, e.g.

```
warning: public function `shell` has 3 co-compiled definitions with 2 differing
signatures ...; JIT call sites resolve by exact arg-type match (mangled `$dupN`
variants), falling back to the last definition when types are ambiguous
[compiler_cross_module_private_symbol_collision]
```

but here the two definitions have *identical* signatures, so there is no
arg-type discriminator at all — resolution is positional/last-wins, and no
warning is produced.

## Consequence for anyone writing these tests

Sabotage of a spec importing this symbol must perturb
`simple_web_engine2d_renderer.spl:1170` or the rasterizer beneath it
(`sfnt_glyf.spl`, `backend_software.spl`), **not** `simple_web_renderer.spl:98`.
This is recorded inline as a BINDING NOTE at the top of
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl`.

## Suggested fix

Rename one of the two. The `simple_web_engine2d_renderer` one is the entry that
actually serves callers today, so the lower-risk rename is
`simple_web_renderer.spl:98` — e.g. to
`simple_web_render_html_to_pixels_with_resolved_engine2d_backend`, which also
describes its actual `_resolved_backend_name` behaviour. Extend the existing
`compiler_cross_module_private_symbol_collision` diagnostic to fire on duplicate
public definitions with *identical* signatures, which it currently misses.
