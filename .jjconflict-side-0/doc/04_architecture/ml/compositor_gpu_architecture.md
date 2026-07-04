# Compositor + GPU Engine Architecture (Three-Layer)

## 1. Three-layer model

```
┌──────────────────────┬────────────────────────┐
│  Game 2D frontend    │  Compositor frontend   │
│  (retained mode)     │  (window manager)      │
│  src/lib/gc_async_mut│  src/lib/nogc_sync_mut │
│  /game2d/            │  /compositor/          │
└──────────┬───────────┴─────────┬──────────────┘
           │                     │
           ▼                     ▼
        ┌────────────────────────────┐
        │  CompositorBackend trait   │  ← the selector
        │  src/os/compositor/        │
        └──────────┬─────────────────┘
                   │
         ┌─────────┴──────────┐
         ▼                    ▼
   ┌────────────┐      ┌────────────┐
   │  Software  │      │ Engine2D   │
   │  Rasterizer│      │ (std.gpu)  │
   │  (lib,     │      │ (gc_async) │
   │  no-GC)    │      │            │
   └────────────┘      └────────────┘
```

## 2. Tier boundaries

`src/lib/nogc_sync_mut/` (no-GC, sync, mutable) is the kernel/driver-adjacent tier. It **must not** import from `src/lib/gc_async_mut/` (GC, async). The boundary is enforced by module resolution — violating it breaks baremetal builds.

The OS tier at `src/os/` is the only layer allowed to consume both. `src/os/compositor/` is where the selector lives.

## 3. Game 2D path (TODO #28)

`src/lib/gc_async_mut/game2d/` exposes a retained-mode scene-graph abstraction:
- `Sprite`, `AnimatedSprite` — drawable leaves with frame-index cycling.
- `Scene` — parent node; `update(dt)` recurses; `render(engine, camera)` walks the tree.
- `SpriteBatch` — groups same-texture sprites for a single Engine2D call.
- `Transform2D` — position/rotation/scale with cached world-matrix.
- `Camera2D` — viewport + world↔screen conversion.
- `TileMap` — grid + tileset texture.
- `Game2DEngine` — facade that creates an `Engine2D` and drives a root Scene.

Consumes `std.gpu.engine2d.Engine2D` directly. **Out of scope:** physics, tweening, audio, input.

## 4. Compositor path (TODO #29)

`src/lib/nogc_sync_mut/compositor/` stays a pure-software fallback. Hardware acceleration is a **runtime choice at the OS tier** via `src/os/compositor/display_backend.spl#select_backend(caps)`:

- `caps.has_gpu == true` → `GpuCompositorBackend` (wraps `Engine2D` via `compositor_engine2d.spl`)
- `caps.has_gpu == false` → `FbCompositorBackend` (framebuffer + lib rasterizer)

Both satisfy the `CompositorBackend` trait: `clear`, `fill_rect`, `present`, etc.

## 5. Platform capability detection

`PlatformCaps { has_gpu: bool }`. The `has_gpu` field is populated by the driver probe layer — specifically `src/os/drivers/gpu/gpu_accel.spl` (the VirtIO-GPU detect work from TODO #19).

## 6. Rollback path

- `SIMPLE_FORCE_SOFTWARE_RASTER=1` env var forces the FB path even when `has_gpu=true`.
- Boot-time compositor config can pin the backend explicitly.
- Individual layers can opt out of GPU acceleration by flagging themselves at creation.

## 7. Chromium reference

This mirrors Chrome's `cc` / `viz` / Skia Ganesh separation. Compositor = window-manager primitive (viz). Game engine = alternate frontend (analog to an in-browser Canvas or iframe). Both reduce to GPU commands through a common backend trait — Skia's `GrContext` is our `Engine2D` facade.

See https://chromium.googlesource.com/chromium/src/+/lkgr/docs/how_cc_works.md for the pattern.
