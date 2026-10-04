# `main_2d_vulkan.spl` can never pass: the strict Vulkan lane rejects the showcase's translucent glass rects

- **Filed:** 2026-10-04
- **Area:** `src/app/ui_showcase/hosts/host_2d_vulkan.spl` ×
  `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`
  (`_engine2d_draw_ir_strict_vulkan_primitive_reason`, line ~1388)
- **Status:** OPEN — capability gap, not fixed here

## Symptom

On macOS arm64 with MoltenVK (device opens fine):

```
SIMPLE_SHOWCASE_FRAMES=1 <seed> run src/app/ui_showcase/hosts/main_2d_vulkan.spl
showcase status=fail renderer=vulkan reason=fresh-device-drawir-receipt-rejected
```

The executor's own result (temporary print in `_accept_fresh_device_result`):

```
sel=gpu fb=true fr=strict-vulkan-opaque-rect-required skip=1 rend=0
rb=preflight_rejected h=0 dev=0 ck=0 px=0 exp=76800
```

## Cause

The strict lane admits only an opaque full-surface clear followed by opaque,
unstyled rects, linear strokes and resolved text. The showcase composition is
the glass theme: at 320x240, **16 of its 19 RECT commands are translucent**,
starting with the very first one:

```
reject comp=sp__root               alpha=184 box=0,0,320x240
reject comp=sp__toolbar            alpha=15  box=1,1,318x22
reject comp=sp__linked             alpha=184 box=1,23,318x54
reject comp=sp__panel_left-track   alpha=15  box=2,24,158x52
rects=19 translucent=16 styled=0
```

So preflight fails on command 0 every frame, for every size; the host then
rejects the frame. `main_2d_gpu.spl` with `SIMPLE_GPU_BACKEND=vulkan` renders
the same scene through the general executor and passes.

## Options (owner decision)

- Teach the strict lane source-over blended rects (device-side blend, with a
  matching oracle), keeping its no-CPU-fallback guarantee; or
- give the strict host an opaque-ground composition (flatten the glass root
  over `RASTER_BG` before submission) — a fidelity change, so only with sign-off.

Neither is a showcase-only fix; the rejection token is correct for the lane as
specified.
