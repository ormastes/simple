<!-- codex-research -->

# HTML/CSS Binary Caching Design

## Data Structures

- `WebRenderOptimizationProfile`: cache schema, cache key, static-shell cacheability, static-shell byte estimate, dynamic-region count, render plan.
- `WebRenderCacheResult`: artifact, optimization profile, cache hit/store flags, and resolved cache path.
- `WebRenderStaticArtifactCache`: optional app-level cache with persistent storage plus hot memory fields for the last static shell.
- `WebRenderStaticShellBinaryArtifact`: compact `SWBC1` static-shell plan containing cache key, encoded bytes, full HTML bytes, source byte counts, command count, viewport dimensions, style rule count, text run count, layout payload byte estimate, and cacheability.
- `WebRenderPreparedStaticShellArtifact`: decoded `SWBC1` artifact prepared once for repeated hot reuse.
- `WebRenderStaticShellCommand`: retained static draw command with kind, geometry, and color.
- Cache key format: text key with explicit schema version and escaped fingerprints for title/body/CSS/JS.
- Cache path format: SHA-256 digest of the shared cache key plus `.html`, scoped under the caller-provided cache directory.
- Dynamic markers: `data-simple-dynamic`, `data-live`, `data-ui-patch`, and JS `WebSocket`.

## Algorithms

1. Build a stable request fingerprint from render target, surface, viewport, pixel mode, capabilities, and bounded head/tail fingerprints of title/body/CSS/JS.
2. Count dynamic markers in body/JS.
3. Select `binary_static_shell` when no dynamic markers exist.
4. Select `static_shell_with_dynamic_islands` when dynamic markers exist.
5. In artifact creation, build full HTML once and pass it to IPC JSON generation for Electron/Tauri targets.
6. For static-shell requests, `web_render_cached_static_artifact(cache_dir, req)` reads cached full HTML when present, otherwise builds, stores, and returns the artifact.
7. For repeated static-shell requests, `WebRenderStaticArtifactCache.artifact(req)` checks the hot memory key before touching disk.
8. For dynamic-island requests, cache helpers return a fresh artifact and do not store HTML.
9. For static-shell size measurement, `web_render_static_shell_binary_artifact(req)` emits a compact `SWBC1` plan that is smaller than full generated HTML for representative static shells.
10. The decoded layout payload estimates the compact runtime shape as command slots, style slots, text run slots, and viewport dimensions, distinct from the encoded on-disk plan bytes.
11. For frame-hot reuse, `WebRenderPreparedStaticShellArtifact.prepare(req, encoded)` decodes and validates once, then `cached_result()` serves subsequent hits without re-decoding.
12. `command_list()` returns retained static shell draw commands so frame-hot paths can reuse geometry without re-walking HTML.

## GTK Comparison

`scripts/check-gtk-gui-size-speed-baseline.shs` generates:

- a Simple render-loop benchmark using the lightweight pure software HTML renderer and optimization profile;
- a Simple static-cache hit loop using `WebRenderStaticArtifactCache`;
- a prepared `SWBC1` reuse loop using `WebRenderPreparedStaticShellArtifact`;
- retained command payload bytes and command reuse counts;
- static-shell size evidence for full generated HTML, compact `SWBC1` plan, and decoded layout payload estimate;
- a minimal GTK C program when `pkg-config` exposes GTK4 or GTK3;
- a report under `doc/09_report/`.

GTK speed is reported as unavailable on headless hosts where GTK cannot initialize a display.
