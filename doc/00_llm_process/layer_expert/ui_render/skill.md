# UI Render Layer Expert

## Role

Own layer-specific process knowledge for the shared UI render layer —
`src/lib/common/ui/` (scene/DrawIR types, widget model, backend traits) plus the
Engine2D pixel kernels in the native runtime (`src/runtime/runtime_simd_dispatch.c`)
and `std.gpu.engine2d.*`. Public contract: a **`DrawIrV3Scene`** produced by any
front end (GUI, Web, 2D, WM) and consumed by a backend that turns it into pixels.

This layer is what the four SimpleOS screen targets are being unified onto — see
[feature_expert/simpleos_screens_render_lane](../../feature_expert/simpleos_screens_render_lane/skill.md).

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Layer Links

- Source: [src/lib/common/ui/](../../../../src/lib/common/ui/)
- Design: [doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md](../../../05_design/os/desktop/screen_backend_selection_and_shared_showcase.md)
- Verified-fact ledger for the current campaign:
  [doc/03_plan/os/simpleos/screens/ws_blocker_verification.md](../../../03_plan/os/simpleos/screens/ws_blocker_verification.md)
- Adjacent layers: [os_compositor](../os_compositor/skill.md) (consumes frames),
  [browser_engine](../browser_engine/skill.md) (HTML→pixels; a *different* front
  end onto the same contract).

## Public Contract Notes (2026-08-06)

- **`DrawIrV3Scene` is THE shared render contract.** GUI and Web both already
  produce it. **`app.ui.render` is an unrelated text/HTML *string* contract — it
  is not a render contract and nothing in this layer should be built on it.**
- **`RenderBackend` (`src/lib/common/ui/backend.spl`) is imported by 8 targets
  and never implemented.** The importers: `src/app/ui.electron/backend.spl:6`,
  `ui.none/backend.spl:6`, `ui.tauri/backend.spl:7`, `ui.tui/backend.spl:6`,
  `ui.vscode/backend.spl:7`, `ui.web/backend.spl:6`,
  `src/os/compositor/fb_backend.spl:15`, `browser_backend.spl:16`.
  Beware the name collision: the ~15 files under `std.gpu.engine2d.backend`
  declare a *same-named but different* trait. Grep counts that mix the two are
  wrong. (The only real `create_backend` in the tree is the compiler's, at
  `src/compiler/70.backend/backend.spl:34` — unrelated to UI.)
- **`FramebufferBackend` implements `RenderBackend`** at `fb_backend.spl:133`
  (not `:121`, and **not** `CompositorBackend` — that one is declared at
  `display_backend_core.spl:7` and is not implemented there). **Backend factory
  arms are not uniform**: check the actual trait per arm before adding one.
- **`ScreenHost` (incoming, WS-B) lands additively — never as a rename** of
  `RenderBackend`/`CompositorBackend`. Contract: `size()` +
  `present_scene(DrawIrV3Scene)` + `poll_input() -> HostInputEvent?`, with new
  `HostInputEvent` = `Pointer{x,y,button,pressed,wheel}` | `Key{code,ch,down,mods}`
  | `Resize{w,h}` in this layer.
  > **UNRESOLVED CONFLICT.** The design doc words `ScreenHost` as a
  > **renamed/extended `RenderBackend`** in `backend.spl`; the campaign's
  > standing instruction says additive-only. With 8 live importers a rename is
  > breaking. Reconcile before editing `backend.spl` — see
  > [feature_expert/simpleos_screens_render_lane](../../feature_expert/simpleos_screens_render_lane/skill.md).
- **`WidgetNode` is a handle over a module-global store**, not a value. So
  widget/showcase construction is **"no I/O", not pure** — and **specs must use
  distinct widget-id prefixes or they collide** across examples and files. This
  is the single most common source of confusing cross-spec failures here.
- **No `HalInput` trait exists**; `hal_current.spl:36` is x86_64-hardwired.
  **`InputBackend` remains the input abstraction** — do not add a parallel one.

## Pixel/Perf Reality (WS-D; read before any SIMD work)

- **Pixels are boxed `int64_t`**, via `engine2d_box_pixel` / `engine2d_unbox_pixel`
  (`src/runtime/runtime_simd_dispatch.c:663` / `:667`). They are **not packed
  u32**. Any kernel design assuming packed u32 SIMD lanes is **invalid** and will
  not survive review.
- **Blend allocates even on the native path**: two `malloc`s + three O(n) passes
  per blended row (`:1464-1476`); the malloc-failure fallback is *also* per-pixel
  unbox/blend/box. There is currently **no allocation-free blend path at all**.
  The fix is either box-aware unpack once per span, or attacking the boxing.
- Other measured root causes: the interpreter extern bridge repacks the *whole*
  framebuffer per span (must become O(count)); SIMD alpha-blend is net-negative
  (gather/scatter, no in-place `blend_span`); `simd_fill_row` is slower than
  scalar; blit is never SIMD; no batching or double buffer.
- **`dirty_tiles` are marked at 6 sites and read by nobody** — damage-driven
  present is about *consuming* an existing signal, not adding one.
- Hot-path file map: `src/runtime/runtime_simd_dispatch.c` (box/unbox at :663/:667,
  blend at :1454-1488, box sites :1367 / :1397 / :1470-1487 / :1551; the copy path
  `rt_engine2d_simd_copy_row_u32` :1442 needs no unboxing),
  `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl:372-392`,
  `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:621`/`:764`,
  `src/compiler_rust/compiler/src/interpreter_extern/simd.rs` (the O(framebuffer)
  bridge), `tile.spl` (`get_dirty_tiles()`, unwired).
- **A real duplicate Engine2D implementation exists.** Canonical is
  `src/lib/nogc_sync_mut/gpu/engine2d/`; `src/lib/nogc_async_mut/gpu/engine2d/`
  is a duplicate slated for deletion. Do not patch both — and note that deleting
  a reimplementation *reroutes* callers rather than deduping them.
- **Perf claims require a bench row** from a pinned worktree + deployed native
  binary. Baseline: p50 **2389 ms** vs Cairo **0.032 ms**
  ([doc/09_report/gui_perf_benchmark_2026-07-10.md](../../../09_report/gui_perf_benchmark_2026-07-10.md));
  harness `test/perf/graphics_2d/bench_harness.spl`.

## Unified Packed UI Scene (2026-08-06, lanes L0-L9 all landed)

WM, GUI, Web all write disjoint pre-reserved ranges of one physical
`DrawIrV3Scene` via the `UiPackedProducer` trait
(`ui_scene_slice.spl`), instead of each owning a separate scene. Full
handoff notes, landed commit hashes, and known gotchas (id-rebasing,
GROUP-wrapper trap, hit-testability asymmetry, cross-producer
`component_id`/generation consistency):
[feature_expert/unified_packed_ui_scene](../../feature_expert/unified_packed_ui_scene/skill.md).

## Tests / Smoke Checks

- Unit specs: `test/01_unit/lib/common/ui/`.
- **Known-broken imports:** four specs import a **nonexistent**
  `common.ui.backend_factory`. They **fail loudly** (`no examples executed` /
  `1 total, 0 passed, 1 failed`) — an earlier claim that they were *silent false
  coverage* was empirically **refuted**. Worth fixing; not a fail-open hole.
  (The count is four, not seven — three other files only name it in `@cover`
  comments.)
- Watch the [os_compositor](../os_compositor/skill.md) entry's toolchain notes:
  deployed-binary extern gaps have repeatedly made specs in this area red for
  reasons unrelated to the code under test.

## Dependent Feature Experts

[simpleos_screens_render_lane](../../feature_expert/simpleos_screens_render_lane/skill.md),
[wm_gui_window_drawing](../../feature_expert/wm_gui_window_drawing/skill.md),
[rendering_inside_rendering](../../feature_expert/rendering_inside_rendering/skill.md),
[ui_testing](../../feature_expert/ui_testing/skill.md),
[interaction_input_routing](../../feature_expert/interaction_input_routing/skill.md),
[unified_packed_ui_scene](../../feature_expert/unified_packed_ui_scene/skill.md).

## Update Rule

When this layer's public contract, source ownership, tests, architecture, or
verification requirements change, update this skill with the new links and
handoff notes. Record contract *additions* (e.g. `ScreenHost`) explicitly as
additive so a later agent does not read them as renames.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
