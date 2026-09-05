<!-- codex-research -->

# HTML/CSS Binary Caching Architecture

## Decision

Use `common.ui.web_render_api` as the ownership boundary for render cache identity, binary artifact metadata, and static/dynamic render planning. Renderer hosts (`ui.web`, Electron, Tauri, pure Simple browser, SimpleOS compositor) consume the same request/artifact contract and must not invent separate cache-key or binary-artifact metadata payloads.

## Layers

1. Shared API layer: request/artifact shape, cache schema version, cache key, optional binary artifact metadata, static-shell profile, dynamic-island count, and complete webview transport bundles.
2. Static cache layer: persistent HTML artifact lookup/store for cacheable static shells, keyed by the shared cache key digest.
3. Static binary-plan layer: compact `SWBC1` render-plan artifact for static shells, with decode/validate, layout payload fields, retained draw commands, and prepared reuse support for frame-hot paths.
4. Renderer layer: HTML/CSS parsing, static shell compilation, current compact static-shell plan decode/validate, future full DOM/style/layout binary artifact encode/decode, retained scene graph.
5. Host adapter layer: web socket, IPC, compositor, and native host details. This layer can transport artifacts but does not own cache identity.
6. Benchmark/report layer: host-specific comparison scripts for Simple versus GTK/Qt/etc.

## First Milestone

The first implementation exposes deterministic cache metadata, removes duplicate full-HTML generation for Electron/Tauri IPC artifact creation, adds `src/app/ui.web/render_cache.spl` as a persistent static-shell HTML cache with a hot in-memory front layer, emits compact `SWBC1` static-shell binary-plan artifacts with layout payload fields, carries binary plan identity through `WebRenderArtifact`, supports retained draw-command reuse after one decode/validation step, and adds `WebRenderTransportBundle` as the common render/input/snapshot/patch/host-window serialization proof for Electron and Tauri. Dynamic-island requests bypass static storage until retained invalidation and full DOM/style/layout binary artifact storage are designed.

## Future Milestones

- Binary DOM/style/layout artifact store keyed by the shared cache key plus dependency/resource fingerprints.
- Retained display-list/scene graph with dirty-region invalidation.
- Virtualized list/table/tree/editor primitives.
- Backend-neutral 2D command IR with CPU reference and optional Vulkan/Metal/CUDA lowering.
