<!-- codex-research -->
# Simple 2D / Skia / RenderDoc hardening: current-source audit

Date: 2026-09-26. Status: scoped research and proposed extension; no GPU qualification claimed.

## Evidence and scope

Input: `/Users/ormastes/Downloads/simple_2d_skia_renderdoc_2026-09-25.zip`, especially `REPORT.md`, `docs/implementation_tasks.md`, corpus and prototype. Its inspected snapshot is `7345ba1951ccb940c8e50ee439d5c97a9d4e3c95`. Bundle claims are historical evidence, not current checkout test results. Its 18 exporter mock tests and repeatable Chromium software screenshots do not establish native Vulkan correctness. Its Skia C++ prototype was uncompiled.

Current authoritative source observations:

- `src/lib/skia/bridge/engine2d_bridge.spl` offers `skia_render_picture_on_engine2d_reported` and the pixels-only convenience call. It reports skipped operations, truncates geometry, and documents cross-module interpreter mutation loss. Preserve that caveat until a concrete runtime proof replaces it.
- `src/lib/common/ui/draw_ir.spl`: `DrawIrPoint`, `DrawIrRect` and `DrawIrGlyphRunPayload.xs/ys` use integer coordinates. Any fractional migration must cover producer, serializer, diff/patch and consumer together.
- `src/app/ui/renderdoc_diff/events.spl` is already dirty in this checkout and now includes `_is_sha256` and missing graphics-evidence rejection. This is concurrent working-tree progress, not evidence that the ZIP was mistaken or that these changes passed runtime verification.
- `src/app/ui/renderdoc_diff/align.spl` compares event target/order/hash diagnostics. Cross-renderer pixel admission needs a separate contract; equivalent pixels can result from different compute/draw streams.
- Existing accepted `doc/04_architecture/simple_2d_renderdoc_backend_equivalence.md` and its detail design define `BackendRenderRecord`, provenance, target/readback and equivalence validation. Reuse these owners instead of a parallel public capture schema.

## Integration findings

The compatibility API `std.skia` and an actual upstream Skia provider require distinct identities. Web layout, CSS stacking/backdrop roots and shaping remain producer responsibilities. GUI widgets and direct 2D consume the same shared drawing boundary. Capture chooses explicit completed output resources and preserves provenance; arbitrary first attachments and encoded PNG hashes cannot establish visual equivalence.

## Knowledge and ownership

Common guidance located through existing `.spipe/spipe` compatibility route; its skills/wiki indexes and local ownership guide were inspected. Registry has no exact route for this feature. Longest-prefix matches exist for engine2d/browser_engine, broad library and app scopes; receipt records the gap without editing the already-dirty registry. No private scopes accessed. Existing unrelated dirty files and active Codex processes were observed and preserved.

## Unresolved work

Fresh native Vulkan/RenderDoc replay, pinned upstream Skia build, complete DrawIR migration, pinned multilingual fonts, and user-selected broader requirements remain open. Existing reported Skia defects must be reproduced individually; no blanket closure follows from this audit.

## Existing decisions reconciled

The unified-surface feature options already select producer-owned models feeding `DrawIrComposition -> UiIr` with Vulkan first. Its NFR selection remains pending. This hardening study extends that direction and the accepted backend-equivalence evidence capsule; it does not establish competing architecture choices. The prior agent-task plan remains the shared lowering ownership authority.
