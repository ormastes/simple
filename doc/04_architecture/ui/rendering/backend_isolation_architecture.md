# Rendering Backend-Isolation Architecture

**Status:** ACTIVE (2026-07-06) · **Scope:** the layering contract between apps and render backends.

**Reads-with:**
- Plan: [`doc/03_plan/ui/rendering/backend_isolation_plan.md`](../../../03_plan/ui/rendering/backend_isolation_plan.md)
- Design: [`doc/05_design/ui/rendering/draw_ir_multibackend_design.md`](../../../05_design/ui/rendering/draw_ir_multibackend_design.md) § "Layering: app-level backend isolation (2026-07-06)"
- Dev guide: [`doc/07_guide/ui/rendering/backend_isolation_guide.md`](../../../07_guide/ui/rendering/backend_isolation_guide.md)
- Related arch: [`../engine_2d.md`](../engine_2d.md), [`../drawing_stack.md`](../drawing_stack.md), [`../shared_ui_contract.md`](../shared_ui_contract.md)

---

## Principle

Apps never touch a rendering backend or a `rt_*` extern. They name an **engine** on a **facade**;
the facade resolves the engine and owns all backend/FFI contact. This keeps three concerns split:
*what to draw* (app), *which engine* (facade selection by name), *how it reaches the GPU/CPU*
(backend + `rt_*`). Three facades share one shape — `create(name, …)` + a small verb surface —
so an app learns one pattern and reuses it across all lanes.

## Layer table

| Layer | Owns | May call down to | May declare `rt_*`? |
|---|---|---|---|
| **App / examples / UI libs** | scene, HTML, window intent | facades only | **No** |
| **Facades** (`Simple2D` / `WebRenderer` / `GuiRenderer`) | engine selection by name, verb surface | Engine2D, backend impls, designated io/ffi facades | Only inside the facade's own backend impls |
| **Engine2D** (`RenderBackend`/`Engine2DExtended`) | draw ops, backend dispatch, caches, SIMD | concrete backends | via backend impls |
| **Backend impls** (`src/lib/**/gpu/**`) | metal/vulkan/directx/software/cpu_simd, chromium, native WM | `rt_*` runtime | **Yes** |
| **Runtime `rt_*`** (Rust seed / io / ffi) | window/event, timing, GPU buffers, SIMD kernels | — | is the FFI |

## The three facades (one shape)

```
                          APP  /  EXAMPLES  /  UI LIBS
                                    │  (names an engine on a facade — no rt_*, no backend classes)
        ┌───────────────────────────┼───────────────────────────┐
        ▼                           ▼                           ▼
 ┌─────────────┐            ┌────────────────┐          ┌────────────────┐
 │  Simple2D   │            │  WebRenderer   │          │  GuiRenderer   │
 │  (Engine2D) │            │(WebRenderBack.)│          │  (P3 Gap A —   │
 │             │            │                │          │   not built)   │
 │ create_     │            │ web_render_    │          │ GuiRenderer.   │
 │ requested_  │            │ backend(name,  │          │ create(name,…) │
 │ backend(    │            │  w,h)          │          │                │
 │  w,h,name)  │            │ .render_html_  │          │ window/session │
 │             │            │  to_pixels()   │          │ /present       │
 └──────┬──────┘            └───────┬────────┘          └───────┬────────┘
        │ name ∈                    │ name ∈                    │ name ∈
        │ {metal,vulkan,            │ {chromium,                │ {electron,
        │  directx,software,        │  pure_simple}             │  gui_renderer_core}
        │  cpu_simd,…}              │                           │
        ▼                          ▼                            ▼
 ┌─────────────┐          chromium→ Electron OSR        electron → tools/electron-shell
 │  concrete   │          pure_simple ─────────┐        gui_renderer_core ─┐
 │  backends   │◄─────────────────────────────┘                           │
 │ Metal /     │          (WebRenderer's core engine IS Simple2D)         │
 │ Vulkan /    │                                                          ▼
 │ DirectX /   │                                          CompositorBackend / hosted_entry
 │ Software /  │                                          (os/compositor, os/hosted — native WM)
 │ cpu_simd    │
 └──────┬──────┘
        ▼
   rt_* runtime  (rt_metal_* · NEON/SSE2 row kernels · rt_winit_* · rt_time_* · rt_watchdog_*)
```

Note the key relationship: **WebRenderer's `pure_simple` engine and GuiRenderer's
`gui_renderer_core` engine both resolve *down into* Simple2D/native core** — the facades compose,
they do not duplicate a renderer. "Do not reinvent the GUI" (native core stays `hosted_entry.spl`).

## Allowed-dependency matrix

Rows call columns. ✅ allowed · ❌ forbidden (isolation violation) · — n/a.

| caller ↓ \ callee → | App | Facade | Engine2D | Backend impl | `rt_*` |
|---|---|---|---|---|---|
| **App / examples / UI lib** | ✅ | ✅ | ❌ | ❌ | ❌ |
| **Facade** | — | ✅ (compose) | ✅ | ✅ | ❌ (via backend impl) |
| **Engine2D** | — | — | ✅ | ✅ | ❌ (via backend impl) |
| **Backend impl** | — | — | — | ✅ | ✅ |

The single forbidden reach that today's code commits (see plan P0): **App → Backend impl** and
**App → `rt_*`** (the two ❌ in the App row). The enforcement gate (plan P2) greps `src/app/**`
for exactly those two edges outside the allowlist.

## Perf anchors preserved by the layering

The facade boundary is a *naming* boundary, not a data-copy boundary. These backend-internal fast
paths are reached unchanged through the facades and must never gain a per-call hop:

| Anchor | Location | Guarantee |
|---|---|---|
| Metal no-mirror fast path | `Engine2D.create_with_backend_fast` `engine.spl:156` → `MetalBackend.use_gpu_only()` `backend_metal.spl:492` | GPU-only, no CPU mirror (28s→1.4s) |
| Batched Metal buffer FFI | `rt_metal_buffer_upload/_download/set_bytes` `backend_metal_runtime_ops.spl:2-4` | one FFI shot per frame |
| NEON/SSE2 row kernels | `simd_fill_row` `simd_kernels.spl:11` → `fill_row_neon/copy_row_neon` `engine2d_simd_ops.rs:95,161` | runtime-feature-detected span fills |
| Browser pixel cache | `WebRenderPixelArtifactCache` `web_render_pixel_backend.spl:111` → `SimpleWebEngine2DStaticPixelCache.pixels_for_html` `simple_web_engine2d_renderer.spl:66` | single-slot last-html memo, cache-first per frame |

## Known intentional exception (lint must special-case)

`simple_web_engine2d_render_html_pixels` (`simple_web_engine2d_renderer.spl:808`) draws a narrow set
of recognized shapes through `SimpleWebHeuristicSurface` (`:5`) — a bespoke `[u32]` buffer that
bypasses Engine2D on purpose (micro-fast-path). This lives in the backend layer, so it is *allowed*
there; a "browser rendering only touches pixels via Engine2D" lint must special-case it as a known
intentional bypass, not flag it.
