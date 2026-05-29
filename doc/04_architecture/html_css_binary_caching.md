<!-- codex-research -->

# HTML/CSS Binary Caching Architecture

## Decision

Use `common.ui.web_render_api` as the ownership boundary for render cache identity and static/dynamic render planning. Renderer hosts (`ui.web`, Electron, Tauri, pure Simple browser, SimpleOS compositor) consume the same request/artifact contract and must not invent separate cache-key payloads.

## Layers

1. Shared API layer: request/artifact shape, cache schema version, cache key, static-shell profile, dynamic-island count.
2. Renderer layer: HTML/CSS parsing, static shell compilation, future binary artifact decode/encode, retained scene graph.
3. Host adapter layer: web socket, IPC, compositor, and native host details. This layer can transport artifacts but does not own cache identity.
4. Benchmark/report layer: host-specific comparison scripts for Simple versus GTK/Qt/etc.

## First Milestone

The first implementation exposes deterministic cache metadata and removes duplicate full-HTML generation for Electron/Tauri IPC artifact creation. This creates the API surface needed for persistent binary cache storage without forcing that storage into this change.

## Future Milestones

- Persistent binary artifact store keyed by the shared cache key plus dependency/resource fingerprints.
- Retained display-list/scene graph with dirty-region invalidation.
- Virtualized list/table/tree/editor primitives.
- Backend-neutral 2D command IR with CPU reference and optional Vulkan/Metal/CUDA lowering.
