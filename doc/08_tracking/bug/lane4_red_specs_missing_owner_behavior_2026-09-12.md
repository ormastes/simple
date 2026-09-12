# Lane-4 red specs that stay RED: missing owner-module behavior (2026-09-12)

Status: OPEN. Host macOS arm64 (M4), seed `build/cargo-r2/release/simple`
(39528776 / 1789199850), `SIMPLE_EXECUTION_MODE=interpreter
SIMPLE_TIMEOUT_SECONDS=0`, one spec at a time, 600 s cap. Base
`origin/main@f38ceb0f804`.

These four are classification (d): the spec asks for behavior that does not
exist. They are NOT stale oracles and were deliberately not "fixed" by editing
the assertion, because that would turn a real gap into a false green. The other
five specs in the same lane were repaired and are green — see the lane commit.

## 1. `test/01_unit/browser_engine/anonymous_block_spec.spl` — 4 examples, 4 failures

`semantic: function layout_context_new not found`, all four examples.

Root cause: the M14 public layout API is half-built.
- `src/lib/gc_async_mut/gpu/browser_engine/layout_m14_types.spl:11-52` defines
  `LayoutContext`, `layout_context_new`, `LineBox`, `LayoutBox`.
- `src/lib/gc_async_mut/gpu/browser_engine/layout.spl:187` says
  `export layout_block` — **and `layout_block` is defined nowhere in the tree**
  (`/usr/bin/grep -rn layout_block src/lib` returns only `_layout_block_be`, a
  different, `BeLayoutBox`-typed internal in `layout_core.spl:59`). `layout.spl`
  also re-exports none of the M14 types the spec imports from it.

So the spec's import list (`layout.{LayoutContext, LayoutBox, layout_block,
layout_context_new}`) names one symbol that exists in a sibling module and one
that exists nowhere. The AC-3 behavior itself — CSS anonymous block generation
wrapping inline runs that are siblings of block boxes — has no implementation:
`is_anonymous` appears only as a `LayoutBox` field declaration and its `false`
initializer, and nothing ever sets it true.

Unblock condition: implement the M14 `layout_block(node, ctx) -> LayoutBox`
over the public `LayoutBox` type with anonymous-block generation, and make
`layout.spl` export the M14 types alongside it (or repoint the spec at
`layout_m14_types`). Not a ≤80-line change and not attempted here.

## 2. `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_list_spec.spl` — 1 example, 1 failure

Was `semantic: class VulkanBackend has no field named
rect_list_device_dispatch_count`. The counter is now real (added in this lane,
`backend_vulkan.spl` + `backend_vulkan_helpers.spl`), so the failure has moved
to the honest one: `expected 0 to equal 1`.

Root cause: `VulkanBackend._draw_rect_filled_impl` (`backend_vulkan.spl:1264`)
dispatches each rect on its own through `_dispatch_framebuffer_checked`; it
never coalesces consecutive opaque rects into the rect-LIST lane. Only the
explicit `draw_rect_list_filled` API (`:1311`) reaches `_enqueue_rect_batch*`.
`enable_frame_batching()` (`:1077`) only sets a flag; it installs no coalescer.
The spec asks for auto-coalescing of ordered opaque `draw_rect_filled` calls
into ONE device dispatch, preserving list order.

Unblock condition: a rect-list coalescer on the frame-batching path. The counter
this lane added is the oracle it should be measured against.

## 3. `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl` — 69 examples, 7 failures (was 25)

19 of the 25 were lost colour constants and are fixed (restored from the sibling
`draw_ir_box_effects_spec.spl:38-41`). The remaining 7 are lost spec-LOCAL
helpers that were never anywhere in the tree:

- `_css_background_style(mode, x, y, w, h)` — 3 failures (:561, :980-988, and
  the fresh-device preflight example)
- `_css_background_result(style, ...)` — 3 failures (:867-1035)
- `engine2d_draw_ir_payload_summary` — 1 failure. Only
  `engine2d_draw_ir_payload_summary_sdn_compat`
  (`src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl:152`) exists.

The first two take style metadata and return a rendered comparison result; their
bodies are not recoverable from the call sites, and guessing them would fabricate
the oracle. Left RED deliberately.

Unblock condition: recover the helpers from the commit that split this file, or
rewrite them against the CSS-background lowering contract they are asserting.
For the third, either export a non-`_sdn_compat` summary or repoint the spec.

## 4. `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` — 110 examples, 36 failures (was 39)

Three were a missing `use` for `WebRenderBackend` and are fixed. The remaining
36 are heterogeneous and exceed one lane:

- lost spec-local helpers, same pattern as (3): `_draw_ir_command_index` (5),
  `_wm_material_section` / `_wm_material_section_with_backdrop` (2),
  `_draw_ir_text_command` (1), `_count_non_color_rect` (1), `partial_html` (1)
- real value mismatches: ~14 `expected N to equal N`, 4 `expected true to equal
  false`, 3 `to be greater than`, 2 `expected software to equal opencl`
- 1 `invalid assignment: cannot index assign value of type array`

**Do not chase the `[web-style-producer] css-props-stage1/stage2 ... =0` trace
lines** printed alongside these failures. They look like one shared root cause
and are not: `simple_web_html_layout_renderer_core.spl:922` and `:937` document
that a zero is the CORRECT and expected output for a `<style>` block carrying no
`:root` custom properties, and both were "PROVEN SILENT 2026-08-09 in the WM
lane". Most of these examples use plain CSS with no variables.

Unblock condition: split by cluster — helper recovery first (it may change what
the value mismatches read), then the object-fit / text-decoration / font
shorthand groups separately.

## Environment note (classification (c)), not a defect

`backend_vulkan_image_exact_scratch_spec` is GREEN, but only without
`SIMPLE_VK_IMAGE_UPLOAD=u32`. That variable selects the typed u32 upload lane;
the spec measures the BYTE lane's staging-array packing, so under `u32` every
counter legitimately reads zero and 2 of its 3 failures were purely the
prescribed environment. Run this file with
`SIMPLE_2D_BACKEND=vulkan SIMPLE_VK_READBACK=native` and no image-upload
override.

## Lane-collision note

`doc/03_plan/infra/macos_open_bugs_fix_lanes_round2_2026-09-12.md` assigns
`backend_vulkan_image_exact_scratch_spec.spl` to lane 2 and
`backend_metal_font_spec.spl` to lane 3, while lane 4's brief also lists them.
Both were repaired here as oracle fixes; dedupe against those lanes.
