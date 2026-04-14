# D1 — `fill_rect` Edge Semantics Doc-Test Plan

**Date:** 2026-04-14
**Parent:** `doc/03_plan/sys_gui/gui_layer_contract_fix_plan.md` (item D1)
**Status:** ready to execute

## 1. Scope

Pin `fill_rect(x, y, w, h, color)` to the half-open rectangle `[x, x+w) × [y, y+h)` across every `CompositorBackend` impl and the `RenderBackend.draw_rect_filled` trait that Engine2D-backed compositors dispatch into. Scope is limited to **documentation and one pixel-level regression spec**. No pixel loops change. Out of scope: D2 (glass externs) and D3 (Engine2D `draw_text` bg handling) — tracked separately in the parent plan.

## 2. Current state on `origin/main`

| Backend | File:line (origin/main) | Pixel-level semantics | Matches contract? |
|---|---|---|---|
| `FbCompositorBackend.fill_rect` | `src/os/compositor/display_backend.spl:15-17` — `self.fb.fill_rect(x.to_u32(), y.to_u32(), w.to_u32(), h.to_u32(), c)` | Delegates to `FramebufferDriver.fill_rect` at `src/os/drivers/framebuffer/fb_driver.spl:96-112`, body `while row < h` / `while col < w` | yes (exclusive) |
| `GpuCompositorBackend.fill_rect` | `src/os/compositor/display_backend.spl` inside `impl CompositorBackend for GpuCompositorBackend` — `self.gpu.fill_rect(x.to_u32(), ...)` | Delegates to `VirtioGpuDriver.fill_rect`; same `while row < h` shape | yes (assumed, needs pin) |
| `HostedCompositorBackend.fill_rect` | `src/os/compositor/hosted_backend.spl:73-80` — `rt_winit_buffer_fill_rect(_hosted_buffer_id, xi, yi, wi, hi, c)` | Rust-side FFI, winit native pixel buffer; per `rt_winit_buffer_fill_rect` extern at line 20 | yes (contract-by-extern) |
| `BrowserCompositorBackend.fill_rect` | `src/os/compositor/browser_compositor_backend.spl:49-61` — `while row < h: ... while col < w: self.pixel_buffer[py * self.w + px] = color` | pure Simple, half-open | yes (exclusive) |
| `Engine2dCompositorBackend.fill_rect` | `src/os/compositor/compositor_engine2d.spl:96-97` — `self.engine.draw_rect_filled(x, y, w, h, color)` | Forwards to Engine2D facade → `RenderBackend.draw_rect_filled` | yes (transitive) |
| `CpuBackend.draw_rect_filled` | `src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl:104-108` — `var row = y; while row < y + h: _hline(self, x, row, w, color)` (and `_hline` walks `col < w`) | half-open | yes (exclusive) |
| `BaremetalBackend.draw_rect_filled` | `src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl:105-` | clips then delegates to `fb.fill_rect` | yes (transitive on fb) |
| `RenderBackend` trait sig | `src/lib/gc_async_mut/gpu/engine2d/backend.spl:37` — `me draw_rect_filled(x: i32, y: i32, w: i32, h: i32, color: u32)` | no docstring on the trait method | **drift** — unwritten |
| `CompositorBackend` trait sig | `src/os/compositor/display_backend.spl` (trait block, above `impl FbCompositorBackend` at line 82) | no docstring | **drift** — unwritten |
| `electron_capture.spl` | `src/os/compositor/electron_capture.spl` | no `fill_rect` impl (capture-only, not a paint backend) | n/a |
| `browser_backend.spl` | `src/os/compositor/browser_backend.spl` | no `fill_rect` symbol; the browser paint path is `browser_compositor_backend.spl` | n/a |

**Correction to parent plan:** parent claims `compositor_engine2d.spl` contains a stale "inclusive" comment. On `origin/main`, `git show origin/main:src/os/compositor/compositor_engine2d.spl | grep -i 'inclusive\|exclusive'` returns **no matches**. The header (lines 1-44) describes only the wrapping strategy. The inclusive-vs-exclusive claim in the parent plan is stale — most likely resolved in an earlier commit — and D1's "remove the comment" action is already done. This plan therefore replaces "remove the comment" with "add a positive docstring" so the contract cannot re-drift.

## 3. The contract to lock

`fill_rect(x, y, w, h, color)` paints exactly the pixels at integer coordinates `(px, py)` where `x <= px < x + w` and `y <= py < y + h`. The right column `x + w` and the bottom row `y + h` are **excluded**. A call with `w <= 0` or `h <= 0` is a no-op; backends MUST NOT paint any pixel. Negative `w`/`h` are **undefined behavior today** — verified on `backend_cpu.spl:104-108` and `browser_compositor_backend.spl:49-61`, both of which silently no-op because the `while row < y + h` / `while row < h` loop predicate fails on the first iteration. `FbCompositorBackend` is worse: `display_backend.spl:17` casts `w.to_u32()` / `h.to_u32()`, so a negative `i32` wraps to a near-4-billion `u32` and the underlying `fb_driver.fill_rect` at `fb_driver.spl:96-112` would run until it clamps to `self.width`/`self.height` — effectively "paint to edge." This is a hazard but is out of D1's scope; the contract documents negative w/h as **undefined**, not "clipped."

## 4. Doc-test approach — two options

**(a) Single cross-backend spec** at `test/unit/common/ui/fill_rect_edges_spec.spl`. Runs one tiny canvas through every in-process backend that can be constructed without host FFI (`BrowserCompositorBackend`, `Engine2dCompositorBackend` wrapping `CpuBackend`) and asserts the pixel boundary. Pros: one source of truth; impossible to pin one backend and forget another; matches the wm_compare style already in `test/unit/os/compositor/`. Cons: does not exercise `HostedCompositorBackend` (winit FFI) or `GpuCompositorBackend` (virtio-gpu) without a system harness; those two are contract-by-extern.

**(b) Per-backend inline doctest** next to each `fill_rect` impl. Pros: lives with the code. Cons: five near-identical spec fragments, no shared fixture, and the FFI backends still cannot be exercised inline.

**Recommendation: (a).** The three backends we can pin directly (`BrowserCompositorBackend`, `CpuBackend` via `Engine2dCompositorBackend`, and — if reachable without FFI — a mock that exercises the Engine2D wrapper code path) cover every pure-Simple pixel loop. `HostedCompositorBackend` and `GpuCompositorBackend` are documented in the trait docstring (§6) and verified by the existing `test/system/os/hosted_wm_system_test.spl` golden-pixel harness. One spec, one fixture, one set of assertions — minimal maintenance.

## 5. Test fixture design

- Canvas: 16×16, `BrowserCompositorBackend.new(16, 16)` zero-initialized.
- Paint: `backend.fill_rect(2, 2, 4, 4, 0xFFFF0000)`.
- Expected colored pixel set: `{(px, py) | 2 <= px <= 5 AND 2 <= py <= 5}` — exactly 16 pixels.
- Expected uncolored pixels that pin the edge:
  - `(6, 2)` through `(6, 5)` — right edge EXCLUSIVE
  - `(2, 6)` through `(5, 6)` — bottom edge EXCLUSIVE
  - `(1, 2)` and `(2, 1)` — left/top edge untouched
- Zero-size case: fresh backend, `backend.fill_rect(4, 4, 0, 5, 0xFFFF0000)` — assert `read_pixel(4, 4) == 0` (no-op).
- Repeat the red-square assertions on `Engine2dCompositorBackend` wrapping `CpuBackend` over a 16×16 `[u32]`. Use `cpu.read_pixel` (already present in `backend_cpu.spl`) for the assertions.

## 6. Files to change

| File | Change |
|---|---|
| `src/os/compositor/display_backend.spl` | Prepend a docstring to the `fn fill_rect` line in the `trait CompositorBackend` block (just above the `FbCompositorBackend` impl around line 82). Text: `"""Paint columns [x, x+w) and rows [y, y+h). Right/bottom edge EXCLUSIVE. Zero w or h is a no-op. Negative w/h is UNDEFINED — do not rely on clipping."""` |
| `src/lib/gc_async_mut/gpu/engine2d/backend.spl:37` | Add the same docstring to `me draw_rect_filled` in the `RenderBackend` trait. |
| `src/os/compositor/compositor_engine2d.spl:96` | Add a one-line comment above `me fill_rect`: `# Edge semantics: [x, x+w) × [y, y+h). See CompositorBackend.fill_rect contract.` Do **not** reintroduce any "inclusive" wording. |
| `test/unit/common/ui/fill_rect_edges_spec.spl` | **New file.** Implements the fixture in §5. Two `describe` blocks: `"BrowserCompositorBackend fill_rect edges"` and `"Engine2dCompositorBackend + CpuBackend fill_rect edges"`. Each has `it "paints [x,x+w) × [y,y+h)"`, `it "leaves right and bottom edges untouched"`, `it "no-ops on zero width"`, `it "no-ops on zero height"`. |

No pixel-loop code changes. No trait shape changes.

## 7. Acceptance

- `test/unit/common/ui/fill_rect_edges_spec.spl` exists and passes under `bin/simple test test/unit/common/ui/fill_rect_edges_spec.spl`.
- The spec fails deterministically if any future change flips a `< h` to `<= h` (or equivalent) in `browser_compositor_backend.spl`, `backend_cpu.spl`, or `fb_driver.spl` — verified by locally mutating one operator and re-running.
- `CompositorBackend.fill_rect` and `RenderBackend.draw_rect_filled` both carry the exclusive-edge docstring on `origin/main`.
- `compositor_engine2d.spl` contains no `inclusive` wording; the positive comment at line ~96 is present.
- Parent plan `gui_layer_contract_fix_plan.md` §1 gets a one-line update: "D1 complete — see `d1_fill_rect_contract_doctest.md`."

## 8. Risk & rollout

Risk is near-zero: no production code changes, only a new spec file and three docstrings. If the spec surfaces an off-by-one in `GpuCompositorBackend` (which we cannot reach in-process), open it as a separate bug, do not block D1. Rollout: one commit, no feature flag, no staged deployment. Runs in normal `bin/simple test` on every lane.
