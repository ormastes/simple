# Dev Guide — Rendering from an App Without Breaking Backend Isolation

**Status:** ACTIVE (2026-07-06) · **Audience:** anyone rendering from `src/app/**` or `examples/**`.

**Reads-with:**
- Architecture: [`doc/04_architecture/ui/rendering/backend_isolation_architecture.md`](../../../04_architecture/ui/rendering/backend_isolation_architecture.md)
- Plan (fix recipe): [`doc/03_plan/ui/rendering/backend_isolation_plan.md`](../../../03_plan/ui/rendering/backend_isolation_plan.md)
- Design: [`doc/05_design/ui/rendering/draw_ir_multibackend_design.md`](../../../05_design/ui/rendering/draw_ir_multibackend_design.md)

---

## TL;DR

- Name an **engine** on a **facade**. Never `import` a backend class or declare an `extern rt_*`
  in app code.
- 2D drawing → **Simple2D** (`Engine2D`). HTML → pixels → **WebRenderer**
  (`web_render_backend`). Windows/sessions → **GuiRenderer** (*not built yet — see Gaps*).
- Timing → the `std` time facade. Never `extern rt_time_now_unix_micros`.
- Run the gate before you push: `scripts/check/check-backend-isolation-source-contract.shs`.

## Rendering per lane (correct imports + calls)

### Lane 1 — 2D drawing (Simple2D / Engine2D)

```simple
use std.gc_async_mut.gpu.engine2d.engine.{Engine2D}

# Auto-detect the best backend:
val eng = Engine2D.create(width, height)
# …or request one by NAME (Result, no silent fallback):
val eng = Engine2D.create_requested_backend(width, height, "metal")?
# Draw, then read back:
eng.clear(0xFF202020u32)
eng.fill_rect(x, y, w, h, color)
val pixels = eng.read_pixels()
```

Backend names: `metal`, `vulkan`, `directx`, `software`, `cpu_simd` (plus cuda/rocm/opencl/opengl/
webgpu where built). The metal case automatically uses the no-mirror GPU fast path — you get it for
free by naming `"metal"`; do not hand-construct `MetalBackend`.

### Lane 2 — HTML → pixels (WebRenderer)

```simple
use std.gc_async_mut.gpu.browser_engine.web_render_backend.{web_render_backend}

# engine = "pure_simple" (native Engine2D layout/paint) or "chromium" (real Electron OSR)
val pixels = web_render_backend("pure_simple", width, height).render_html_to_pixels(html)
```

- `pure_simple` routes through the real layout pipeline and the `WebRenderPixelArtifactCache`
  (cache-first, single-slot last-html memo) — you inherit the cache automatically.
- `chromium` captures a real offscreen Electron frame; `.show_live_window(path, w, h, title)` opens
  a live interactive Chromium window (returns `false` for `pure_simple`, which has no live DOM).
- Engine names: `web_render_backend_names()` → `["pure_simple", "chromium"]`.

### Lane 3 — windows / sessions / live GUI (GuiRenderer)

**Not available yet** — see [Gaps](#current-gaps-do-not-work-around). Until `GuiRenderer` lands, a
live native window from an app goes through the existing native GUI core
(`src/os/hosted/hosted_entry.spl` + `src/os/compositor/host_compositor_entry.spl`), **not** by
declaring `rt_winit_*` in your app. Do not copy the current `ui.browser/app.spl` winit block — it is
the very violation this guide exists to remove.

### Timing (any lane)

```simple
use std.nogc_sync_mut.io_runtime.{time_now_unix_micros}
val t = time_now_unix_micros()
# or: use std.nogc_sync_mut.src.time.{now_micros}
```

## Forbidden in app code

| Forbidden | Why | Do instead |
|---|---|---|
| `extern fn rt_*` in `src/app/**` | app must not own FFI | call the facade that wraps it |
| `rt_winit_*`, `rt_time_*`, `rt_watchdog_*` calls | backend/runtime concern | GuiRenderer / `std` time / WatchdogManager facade |
| `import MetalBackend`/`VulkanBackend`/`SoftwareBackend` … | picks a backend directly | `Engine2D.create_requested_backend(w,h,name)` |
| `simple_web_engine2d_render_html_pixels(...)`, `simple_web_render_html_to_pixels_with_engine2d_backend(...)`, `simple_web_layout_render_html_*` | backend-engine entrypoints | `web_render_backend(name,w,h).render_html_to_pixels(html)` |

Exception: `src/app/interpreter/ffi/**` legitimately owns interpreter runtime FFI
(`rt_ast_*`, `rt_env_*`, `rt_error_*`) — it is on the allowlist.

## Running the gate

```bash
scripts/check/check-backend-isolation-source-contract.shs
```

It runs on the pure-Simple self-hosted binary (rejects the Rust seed), greps `src/app/**` and
`examples/**` for `extern rt_*` and backend-engine calls outside the allowlist, runs
`check` + `test`, and prints `backend_isolation_violations=<n>` plus a markdown report under
`doc/09_report/`. Nonzero exit on any violation. It is wired into `bin/simple build check` and the
pre-commit hook.

**Allowlist (where `rt_*` / backend-engine calls are OK):**
```
src/lib/**/gpu/**   src/lib/**/io/**   src/lib/nogc_sync_mut/**
src/app/interpreter/ffi/**   src/os/compositor/**   src/os/hosted/**
```

## Adding a new backend UNDER a facade (not a new facade)

1. **Implement** the backend in `src/lib/**/gpu/**` behind the existing trait
   (`RenderBackend`/`Engine2DExtended` for Simple2D). This module is where `rt_*` externs live.
2. **Register the name** in the single selection source — `Engine2D.create_requested_backend`
   (`engine.spl:183`, add one `if requested_backend == "yourname"` block) and the priority order
   (`helpers_availability.backend_default_priority_order` / `renderer_select.spl`). For WebRenderer,
   add the name to `web_render_backend_names()` and a branch in `render_html_to_pixels`.
3. **Preserve the perf anchors** — if your backend has a GPU fast path, expose it the way Metal does
   (`create_with_backend_fast` / `use_gpu_only`), keep buffer FFI batched (one shot per frame), and
   route span fills through `simd_fill_row`. Never add a per-primitive FFI hop.
4. **Do not add a new facade or a parallel renderer.** New engines plug *under* Simple2D /
   WebRenderer / GuiRenderer. Only build a facade if a genuinely new lane appears (and then mirror
   the `create(name, …)` shape).
5. **Prove it** with a spec that drives the *facade* by name and asserts readback provenance (see
   the SPipe skill § "Backend isolation in UI specs").

## Current gaps (do not work around)

If your task needs one of these, the correct move is to build the facade per the plan's P3 — **not**
to reach past it with `rt_*` or a backend call:

- **GuiRenderer** does not exist (blocks native window/event from apps) — plan P3 Gap A.
- **WebRenderer has no app callers**; `bin/simple browser --backend=X` selects only the Engine2D
  backend, not chrome/core — plan P3 Gap B.
- **WebRenderer cannot pick the Engine2D backend** for the `pure_simple` path (hardcodes `"auto"`) —
  plan P3 Gap C. Until fixed, `cpu_simd`/`metal`-specific web renders can't be requested by name.
- **WatchdogManager** does not exist (blocks `rt_watchdog_*` in the interpreter) — plan P3 Gap D.
- **No draw-IR / software-only readback facade** — plan P3 Gap E.
