# UI Render Layer Expert

Mission-critical DrawIR/Engine2D and external RenderDoc/Vulkan evidence rows
are tracked by `doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`.

## Role

Own layer-specific process knowledge for the shared UI render layer —
`src/lib/common/ui/` (scene/DrawIR types, widget model, backend traits) plus the
Engine2D pixel kernels in the native runtime (`src/runtime/runtime_simd_dispatch.c`)
and `std.gpu.engine2d.*`. Public contract: a **`DrawIrV3Scene`** produced by any
front end (GUI, Web, 2D, WM) and consumed by a backend that turns it into pixels.

This layer is what the four SimpleOS screen targets are being unified onto — see
[feature_expert/simpleos_screens_render_lane](../../feature_expert/simpleos_screens_render_lane/skill.md).

## Pipeline Links

- [research](../../../../.claude/skills/research.md)
- [design](../../../../.claude/skills/design.md)
- [impl](../../../../.claude/skills/impl.md)
- [verify](../../../../.claude/skills/verify.md)
- [release](../../../../.claude/skills/release.md)

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

## Physical 8K80 Admission (2026-08-14)

All physical-display evidence goes through the canonical
[`check-engine2d-vulkan-window-8k.shs`](../../../../scripts/check/check-engine2d-vulkan-window-8k.shs)
wrapper. `ENGINE2D_VULKAN_PHYSICAL=1` uses an existing X11 display and refuses
unless `xrandr` reports an EDID-bearing active `7680x4320` mode at `>=80 Hz`; it also checks
adapter identity, timing, RSS, checksum, timed-readback bytes, completion, and
fallback. The default Xvfb mode is a non-physical device-present proxy and is
never an A6-A8 result.

Keep the [canonical render plan](../../../03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md),
[operator guide](../../../07_guide/app/ui/gui_web_2d_vulkan_setup.md), and
[open physical-display bug](../../../08_tracking/bug/engine2d_vulkan_physical_display_8k_gate_2026-08-12.md)
in agreement. A4-A8 remain BLOCKED on the current host and must resume only as
follows (owner: root Codex merge lane; final reviewer: separate
highest-capability Codex):

| Row | Resume condition and command | Retained record |
|---|---|---|
| A4 | Build the admitted non-seed artifact with the canonical plan command, then execute `SIMPLE_NO_STUB_FALLBACK=1 timeout 300 /usr/bin/time -v -o build/render_perf/draw_ir_damage_8k_bench.time build/render_perf/draw_ir_damage_8k_bench >build/render_perf/draw_ir_damage_8k_bench.stdout 2>build/render_perf/draw_ir_damage_8k_bench.stderr` directly. | [sparse DrawIR report](../../../09_report/drawir_sparse_dynamic_8k_attempt_2026-08-12.md) and `doc/08_tracking/bug/self_hosted_cli_native_build_silent_no_artifact_2026-08-14.md`. |
| A5 | Run `BENCH_TIMEOUT_SECS=300 BUILD_DIR=build/render_perf/gui_8k80 REPORT_PATH=build/render_perf/gui_8k80/gui_8k80_semantic_producer.md bash tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 60 --dpi 300` with that admitted compiler and require native canonical producer receipts. | `build/render_perf/gui_8k80/gui_8k80_semantic_producer.md` and sibling receipts; [retained Web report](../../../09_report/web_renderer_retained_damage_plan_evidence_2026-08-12.md). |
| A6 | Attach a direct-display WSI path, then run `DISPLAY=:0 ENGINE2D_VULKAN_PHYSICAL=1 sh scripts/check/check-engine2d-vulkan-window-8k.shs`; Xvfb cannot unblock it. | [physical-display bug](../../../08_tracking/bug/engine2d_vulkan_physical_display_8k_gate_2026-08-12.md) and `build/check/engine2d-vulkan-window-8k/`. |
| A7 | Only after A4-A6 pass, rerun their canonical rows once and require p95 `<=12500000 ns`, no fallback, known completion, and complete receipts. | [render plan](../../../03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md). |
| A8 | Attach a connector with EDID/mode `7680x4320@80`, run the plan's inventory-and-tee command, then rerun A6. | [physical-display bug](../../../08_tracking/bug/engine2d_vulkan_physical_display_8k_gate_2026-08-12.md). |

## Pixel/Perf Reality (WS-D; read before any SIMD work)

- **Pixels are boxed `int64_t`**, via `engine2d_box_pixel` / `engine2d_unbox_pixel`
  (`src/runtime/runtime_simd_dispatch.c:663` / `:667`). They are **not packed
  u32**. Any kernel design assuming packed u32 SIMD lanes is **invalid** and will
  not survive review.
- **Blend allocates even on the native path**: two `malloc`s + three O(n) passes
  per blended row (`:1464-1476`); the malloc-failure fallback is *also* per-pixel
  unbox/blend/box. There is currently **no allocation-free blend path at all**.
  The fix is either box-aware unpack once per span, or attacking the boxing.
  **Partial progress (2026-08-07):** span-bounded (not row-bounded) SIMD
  kernels landed across all three implementations — native ABI symbols
  `rt_engine2d_simd_blend_span_u32`/`_blend_const_span_u32` in the Rust
  runtime crate (`engine2d_simd_ops.rs`, `ccf1b9f4`, mirroring the earlier
  `fill_span_u32`/`copy_span_u32`), then self-hosted-compiler registration
  (array-return type in `bootstrap_resolved_call_return_type` + LLVM
  `declare`) so the same symbols are reachable under native/AOT/JIT, not just
  the interpreter (`a399483d` for fill/copy, `796d8484` for blend — see
  [mir_lowering layer expert](../mir_lowering/skill.md) for the compiler-side
  half). This does not by itself remove the two-`malloc` row path above; it
  adds a span-granularity alternative alongside it — do not read "SIMD span
  kernels landed" as "the allocation is gone".
- **`simd_config_mode()` nil-env fix (`1365d5a6`):** `rt_env_get` returns
  `nil` (not `""`) for an unset `SIMPLE_2D_SIMD`; the mode resolver only
  guarded `raw == ""` so the unset case fell through to `nil` instead of the
  documented "auto" default. Same nil-vs-empty-string trap as `detect_os()`/
  `detect_arch()` noted elsewhere in this doc — grep for `!= ""` env guards in
  this layer before trusting one handles "unset".
- **`paint_rect` row-bleed fixed (`d129996a`, `paint_chunk_rasterizer.spl`):**
  clipped `py` to `[0, height)` per row but never clipped the x-span/
  `row_offset` to `[0, stride)`, so a negative x (or `x+w` past the right
  edge) computed a `row_offset` landing in an *adjacent row's* flat pixel
  storage and bled the fill across the row boundary. Now the fill span is
  clipped to `[max(x,0), min(x+w,stride))`, symmetric with the existing y
  clip. Regression coverage: negative-x, right-edge-overflow, and partial
  negative-y-overlap cases in `paint_chunk_rasterizer_spec.spl`.
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

## `paint_rect` x-span clip fix (2026-08-07, `d129996a`)

`paint_rect` (`paint_chunk_rasterizer.spl`) clipped `py` to `[0, height)` per
row but never clipped `x`/`row_offset` to `[0, stride)`, so a negative `x`
(or `x+w` overflowing the row) wrote past the row boundary into the next
row's pixels instead of being dropped or truncated. Fixed to clip the x-span
per row before writing, matching the existing y-clip discipline. Any Draw IR
consumer that computes rects from layout math without pre-clamping (e.g. the
overflow-wrap / ellipsis text fixes in
[web_render_css_parity](../../feature_expert/web_render_css_parity/skill.md))
depended on this being correct.

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

## Primitive-lane handoff (2026-08-08)

### Cached sparse DrawIR evidence (2026-08-14)

Use `CachedRenderEntryClosureV1`; see
`doc/07_guide/ui/rendering/cached_render_entry_closure.md`, the canonical
`doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`, and
`doc/09_report/drawir_sparse_dynamic_8k_attempt_2026-08-12.md`. Acceptance
requires an admitted cached carrier, 7680x4320/20-frame execution, one 256x128
changing rectangle, two considered/512 culled commands per frame, nonzero
readback, zero mismatches, stable checksum, backend/fallback and mode,
p50/p95 <= 12.5 ms, max RSS, and binary/source identity. This is executor-only
evidence; it does not prove presentation or physical scanout.

For host-first button, window-drag, CSS/layout, scroll, and font work, use
`doc/07_guide/app/llm/simple2d_primitive_lane_inventory.md` and the linked
architecture/design/test-plan trio. Keep Web, GUI, WM, and 2D semantics on the
shared event -> layout -> `DrawIrComposition` path. A host test is not QEMU GPU
evidence: the QEMU row still requires admitted pure-Simple execution, fenced
device readback, exact parity, font provenance, and warm p95/RSS receipts.
macOS and UNO Q are explicit deferred rows, not fallback passes.

## Engine2D backend readiness guards — scope rule (2026-08-16, from `b10f1b4309c`)

Primitive/readback routing is one five-arm chain repeated at ~28 sites. **Only
the Vulkan arm needs an `.initialized` guard**, and adding one elsewhere is dead
code:

- `virtio_gpu_backend` / `baremetal_backend` — their create paths (L824, L791)
  pass the **same object** as both `backend:` and the sibling field; they cannot
  diverge.
- `cuda_backend` — gated on `selected_backend_name == "cuda"`, set only at L632
  where `cuda.init()` already returned true on that same object.
- `metal` / `opencl` / `rocm` / `software` — **not in the chain at all**; they
  reach drawing only via `self.backend`.
- `vulkan_backend` — the sole arm where `self.backend` is swapped while the
  sibling stays non-nil (`_poison_vulkan_font_surface` L391), plus tests attach a
  bare `VulkanBackend.create()`. An uninitialized Vulkan backend has no
  framebuffer: every dispatch is a silent no-op returning empty pixels.

**Do not "simplify" that guard to `backend_probe_initialized`.** It takes a
`BackendProbeResult` and tests `probe.status == BackendStatus.Initialized`
(`backend_probe.spl:36`); `VulkanBackend.initialized` is a plain `bool` field
(`backend_vulkan.spl:247`). The substitution does not compile. The import at
`engine.spl:57` serves the strict-create paths.

Font offload (`_draw_font_batch_staged` L1607-1720) is a **separate** mechanism:
each target is tried and judged by `quad_index == batch.quads.len()`, recording
`<name>:failed` and falling through. A ledger not ending in a success entry means
the batch was dropped, not offloaded.

Canonicalization (`backend_lane.spl:86`) does `.trim().lower()` before folding
aliases; the preference order list is all-lowercase and must stay that way.

Open, recorded not patched: the rocm arms (L1700, L1941, L2006) do
`if rocm.initialized: self.backend = rocm`, hijacking `self.backend` on an engine
selected as something else — asymmetric with the name-gated cuda arm, currently
unreachable from any construction path.

Guide: `doc/07_guide/ui/engine2d_font_offload_fallback.md`.
Feature expert: `doc/00_llm_process/feature_expert/engine2d_font_offload/skill.md`.
