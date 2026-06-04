<!-- codex-research -->

# HTML/CSS Binary Caching Local Research

Feature subject: smaller/faster Simple GUI and web renderer through binary UI artifacts, static subtree optimization, dependency-aware invalidation, lazy/background component loading, and CPU/GPU backend choices.

## Existing Renderer Boundaries

- `src/lib/common/ui/web_render_api.spl` is the shared cross-surface contract. It owns `WebRenderRequest`, `WebRenderArtifact`, host-window commands, snapshot/patch/input envelopes, JSON serialization, and pixel artifacts. Binary cache identity should extend this boundary instead of creating per-host payloads.
- `src/app/ui.web/backend.spl` maps `UIState` and widgets to HTML through `app.ui.render.html_widgets`, then wraps CSS/JS from the web UI shell.
- `src/app/ui.web/web_runtime_adapter.spl` converts `UISession` snapshots and patch streams into live wire frames. Session, input, patch, and window-manager state should stay out of immutable renderer cache artifacts.
- `src/os/compositor/simple_web_window_renderer.spl` converts themed HTML into a `WebRenderRequest`/`WebRenderArtifact` and blits renderer pixels into a compositor backend.
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl` is the public Simple Web Renderer facade. Its current hot path is HTML-to-pixels through `simple_web_render_html_to_pixels`.
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl` is the actual ARGB pixel fill path currently used by the facade.
- `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`, `dom.spl`, `css.spl`, `layout.spl`, and `layout_box.spl` provide the partial browser-engine model/style/layout path. This is not yet a full HTML/CSS engine.
- `src/app/ui.browser/dom_bridge.spl` has a separate ad hoc HTML/CSS bridge into `std.common.web`/render-scene types.
- `src/app/ui.render/html.spl`, `css.spl`, and `layout.spl` are static HTML/CSS/layout helper libraries for dashboards and exports, not the pixel renderer.

## Existing Cache And Lazy Mechanisms

- `src/lib/common/ui/theme_package.spl` has an in-memory theme package cache invalidated by mtimes over theme package paths.
- `src/app/cache/main.spl` is a generic package cache CLI under the Simple cache directory, not renderer-specific.
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_file_renderer.spl` reads file/about URL HTML and produces placeholder RGBA bytes; it has no persisted renderer cache.
- Existing docs mention `build/browser-font-cache` for `@font-face` materialization. That is font-source caching, not HTML/CSS binary render caching.
- Existing dependency tooling includes import graph, cycles, reverse deps, and why-paths in `doc/06_spec/app/compiler/modules/tooling/simple_deps.md`.
- Existing lazy-init designs prefer explicit/configurable lazy behavior: production may lazy load, while dev/test may eager load for deterministic failures.

## Prior Documentation Constraints

- `doc/02_requirements/feature/shared_wm_renderer_unification.md` selects the shared web render API as the canonical path for `ui.web`, Electron, Tauri, and pure Simple browser rendering.
- `doc/02_requirements/nfr/shared_wm_renderer_unification.md` requires buffer ownership, readback ownership, invalidation, warm startup/init timing, render request latency, and max RSS to be documented.
- `doc/05_design/graphics_backend_acceleration.md` already calls for layout/style cache, glyph cache, paint batching, dirty-rect tracking, GPU upload batching, subtree style/layout invalidation, and render benchmarks versus Chrome/Tauri/C.
- `doc/05_design/engine_2d.md` selects software renderer first. GPU acceleration is an optimization path, not a correctness dependency. The renderer is command-buffer based, with pure types below mutable subsystems and FFI only at leaves.
- `doc/05_design/executable_size_reduction.md` gates size work with explicit byte budgets and startup-path dependency audits. New GUI caching must not pull broad runtime, package, network, TLS, or compression surfaces into startup.
- `doc/05_design/mcp_performance_regression_enforcement.md` provides precedent for compile-to-cache, execute-from-cache, explicit invalidation, startup/RSS/request budgets, and blocking verification.

## Local Conclusions

1. Place cache identity and artifact metadata below adapters, probably near `common.ui.web_render_api` and browser-engine shared code.
2. Cache keys must include HTML/source content, CSS/theme package inputs, dependency graph fingerprint, viewport, backend, renderer version, compiler/runtime version, fonts/assets, pixel-output mode, and feature/capability flags.
3. Live `UISession`, patches, taskbar/window commands, and input state are dynamic protocol state and should not be serialized into immutable render artifacts.
4. Static UI declarations can become renderer containment/cache boundaries. Individual pane contents can remain patchable dynamic islands.
5. The current renderer has partial/fallback behavior, so requirements must distinguish production renderer output from fixture/oracle paths.
6. The new work should reuse existing dependency graph tooling where it can provide import/source fingerprints, but renderer resources need their own asset/theme/font/style invalidation layer.
7. Existing `browser_engine_implementation.md` appears stale where it references `html_parser.spl`/`style_block.spl`; design should verify current file names before implementation.
