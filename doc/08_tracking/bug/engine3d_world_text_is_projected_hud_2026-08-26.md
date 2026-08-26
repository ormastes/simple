# Engine3D world text is projected HUD material, not complete world text

## Status

Open; blocks complete 3D international text, scene occlusion, and native performance claims.

## Evidence

- `src/lib/gc_async_mut/gpu/engine3d/engine.spl:473-518` projects one world anchor and reuses screen-space batch geometry.
- CPU policy routes world material through HUD drawing at `engine.spl:431-438`.
- `src/lib/gc_async_mut/gpu/engine3d/font_hud_material.spl:70-77` varies constant depth while x/y remain screen-space.
- `src/lib/gc_async_mut/gpu/engine3d/vulkan_font_adapter.spl:163-213` uploads the whole atlas after changes and allocates a new native vertex buffer per draw.
- Font Vulkan readback is separate from the CPU scene target, so it does not prove composed scene-plus-text depth behavior.

## Required fix

Implement explicit HUD/screen-label/billboard/world-plane/depth-annotation placement over the canonical shared shaped run and `FontRenderBatch`; integrate with the scene color/depth pass; add CPU parity or fail-closed unsupported modes; add dirty atlas uploads and frame-owned merged instance buffers.

## Owner and unblock condition

- Owner: Engine3D adapter lane with text-layout/font-renderer merge owner.
- Unblock: retained tests prove shared immutable 2D/3D batch identity, scene occlusion and HUD overlay, CPU/device parity, device-origin readback, 100% reachable branch coverage, and cold/warm memory/performance gates.
