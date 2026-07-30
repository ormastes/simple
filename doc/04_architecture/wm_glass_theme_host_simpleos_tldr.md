# WM Glass Theme Architecture — TLDR

- `ResolvedThemePackage` remains the only authority.
- Host projects it once at startup; SimpleOS imports a drift-checked generated
  `ThemeRenderSnapshot` from the same package.
- WM/Web/Draw IR are adapters; Engine2D owns transient effect material.
- SHA-256 manifest and normalized material hashes prove semantic parity.
- No file reads in frame/input paths and no private/legacy renderer counts.

```text
package -> immutable snapshot -> WM + Web -> Draw IR -> Engine2D
                  |                                  |
                  +---------- parity evidence -------+
```

- Runtime switching additionally needs a parent-owned `HostedThemeRuntime`:
  one injected real-mutex store and canonical `theme_package_install_wire_v1`
  created before reads/backends/workers. Worker processes receive
  `theme_init(generation, revision, wire_text)` before HTML and later
  `theme_apply(generation, expected_predecessor_revision, revision, wire_text)`.
  The wire is
  revision-free immutable text; explicit frame revision/hash fields and a
  parent-owned replay payload fence restarts. Hosted wrapper/session owns the
  runtime; shared `HostWmHandle`/core and workers own no store.

- 2026-07-30 rendering boundary: GUI/Web/WM remain semantic Draw IR producers;
  Engine2D alone owns ordered outer/inset raster work, background/inset masks,
  transient pixels, and execution receipts.
- Ordered shadows use bounded all-or-nothing
  `web-box-shadow-layers-v1`; malformed/absent schema falls back once to the
  legacy aggregate. Existing physical corner keys are shared across producers.
- Valid `none` emits typed count `0`; shadow and corner admission are
  independent, so no-shadow boxes keep nonuniform corners.
- Uniform radii retain fast paths; nonuniform/inset work is CPU material.
  Vulkan presentation is not Vulkan device glass, and transient material never
  enters the theme snapshot or Draw IR resources.
- Current outer-shadow silhouettes and nonuniform border outlines remain
  backend limitations; they are documented, not promoted as corner-exact.
- Pure Web parsing is isolated in
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_css_box_effects.spl`;
  transient decode/masks/raster live in
  `src/lib/gc_async_mut/gpu/engine2d/draw_ir_box_effects.spl` with a
  16,777,216-pixel work cap and bounded safe legacy fallback.
