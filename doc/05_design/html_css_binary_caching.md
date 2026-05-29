<!-- codex-research -->

# HTML/CSS Binary Caching Design

## Data Structures

- `WebRenderOptimizationProfile`: cache schema, cache key, static-shell cacheability, static-shell byte estimate, dynamic-region count, render plan.
- Cache key format: text key with explicit schema version and escaped fingerprints for title/body/CSS/JS.
- Dynamic markers: `data-simple-dynamic`, `data-live`, `data-ui-patch`, and JS `WebSocket`.

## Algorithms

1. Build a stable request fingerprint from render target, surface, viewport, pixel mode, capabilities, and bounded head/tail fingerprints of title/body/CSS/JS.
2. Count dynamic markers in body/JS.
3. Select `binary_static_shell` when no dynamic markers exist.
4. Select `static_shell_with_dynamic_islands` when dynamic markers exist.
5. In artifact creation, build full HTML once and pass it to IPC JSON generation for Electron/Tauri targets.

## GTK Comparison

`scripts/check-gtk-gui-size-speed-baseline.shs` generates:

- a Simple render-loop benchmark using the pure software web renderer and optimization profile;
- a minimal GTK C program when `pkg-config` exposes GTK4 or GTK3;
- a report under `doc/09_report/`.

GTK speed is reported as unavailable on headless hosts where GTK cannot initialize a display.
