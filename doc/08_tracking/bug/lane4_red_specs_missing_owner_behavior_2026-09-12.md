# Lane-4 red specs that stay RED: missing owner-module behavior (2026-09-12)

Status: PARTIALLY RESOLVED 2026-09-12 (see the per-item updates below). Host macOS arm64 (M4), seed `build/cargo-r2/release/simple`
(39528776 / 1789199850), `SIMPLE_EXECUTION_MODE=interpreter
SIMPLE_TIMEOUT_SECONDS=0`, one spec at a time, 600 s cap. Base
`origin/main@f38ceb0f804`.

These four are classification (d): the spec asks for behavior that does not
exist. They are NOT stale oracles and were deliberately not "fixed" by editing
the assertion, because that would turn a real gap into a false green. The other
five specs in the same lane were repaired and are green — see the lane commit.

## 1. `test/01_unit/browser_engine/anonymous_block_spec.spl` — RESOLVED 2026-09-12

**4 examples, 4 failures -> 4 examples, 0 failures.** `layout_block` is now
implemented in `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` over the M14
public `LayoutBox`, and `layout.spl` re-exports `LayoutContext`, `LayoutBox`,
`LineBox`, `InlineFragment` and `layout_context_new` from `layout_m14_types.spl`
alongside it, so the spec's import list resolves. It generates a CSS 2.1 §9.2.1
anonymous block box around every maximal inline run that is a sibling of a
block-level box, and none when the container is block-only. The layout root is
resolved by descending through the parser-inserted `#document > html > body`
wrappers while each has exactly one rendered child (confirmed against
`html_tree_builder_debug_dump_bedom`). Verified by sabotage: flipping
`is_anonymous` to `false` returns 2 of the 4 examples to RED.

### original diagnosis

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

## 2. `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_rect_list_spec.spl` — 1 example, 1 failure (unchanged)

Re-confirmed 2026-09-12 under `SIMPLE_2D_BACKEND=vulkan
SIMPLE_VK_READBACK=native`: `expected 0 to equal 1`. Left RED deliberately —
the auto-coalescer needs a buffer on `_draw_rect_filled_impl` plus a frame-end
flush hook that does not exist on that path, which is a feature, not a fix.

### original diagnosis

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

## 3. `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl` — 69 examples, 7 -> 1 failure

Update 2026-09-12: `engine2d_draw_ir_payload_summary` was not a lost spec-local
helper — it was a DANGLING SOURCE REFERENCE. `draw_ir_runtime_adv.spl:16` (and
`gc_async_mut/gpu/engine2d/mod.spl:134`) imported that name from
`draw_ir_runtime_queue`, which only ever defined
`engine2d_draw_ir_payload_summary_sdn_compat`, so every importer of that module
was broken regardless of the spec. The three references are repointed at the
`_sdn_compat` name. The example is still RED but on an honest assertion now:
`expected false to equal true` — `engine2d_draw_ir_adv_batch_runtime_queue`
returns `submitted=false packet=0 drained=0 status=empty queued=false` for a
`vulkan` runtime queue on this host, i.e. nothing is admitted to the host GPU
queue. That is a separate behavior gap in the host-GPU queue admission path,
not a naming defect, and is not repaired here.

**The original "not recoverable, guessing them would fabricate the oracle"
verdict was wrong, and this is the lesson of this lane.** The history search
(`-S 'fn _css_background_style'` across all refs — it takes ~30 minutes on this
repo, which is why the first attempt was abandoned) names `b9a3ff87c95` as the
last commit whose copy of this file still carried both helpers. They are
restored VERBATIM from it, with a comment naming that commit, and six examples
go green without anyone inventing an oracle. Before declaring a lost spec-local
helper unrecoverable, let that search finish.

### original diagnosis

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

## 4. `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` — 110 examples, 36 -> 29 failures

Update 2026-09-12: the "fallback facade" background-color cluster (7 of the 36)
is fixed, with no example regressed (offender lists diffed before/after). Three
real defects, all in the CPU layout/paint path, none of them a stale oracle:

1. **The local CSS color parser knew three named colors.**
   `simple_web_html_layout_renderer_foundation.spl:parse_color` handled
   `#rgb`/`#rrggbb`/`rgb()` plus literally `white`/`black`/`red`, and answered
   0 (transparent) for everything else — so `rebeccapurple` and
   `hsl(120,100%,25%)` painted nothing. It now delegates the unrecognised forms
   to `dom_color.parse_color_value_checked` (the complete browser-engine parser,
   RGBA-packed) and converts to this file's ARGB packing. The three legacy named
   constants are kept ahead of the delegation so existing pixels do not move.
   `currentcolor` is excluded from the delegation: it needs the inherited text
   color, and the delegate would silently answer opaque black.
2. **The canvas background was forced opaque.**
   `_web_canvas_background` returned `bg | 0xFF000000`, so `rgba(0,0,0,0.5)` on
   `<body>` cleared the page to pure black instead of compositing over the white
   base (CSS Backgrounds §2.11.2 + simple alpha `over`). It now blends. The
   blend weights with `256 - a` over a 256 denominator rather than `255 - a`
   over 255: 8-bit alpha is a rounded sample of the authored fraction
   (`0.5` -> 128), and the 255 form reintroduces that rounding loss, landing
   127 where Chrome paints 128.
3. **`currentColor` was never resolved on a background.** Resolved in
   `..._decl_apply.spl` after the whole declaration block is applied, since
   `color` may follow `background-color` in source order (CSS Color §5.2).

**Do not "fix" the rest through
`simple_web_engine2d_renderer.spl:549-569`.** Those lines are
`html.contains("background-color: rebeccapurple; background: #0f8")`-style
matches on the spec's exact HTML strings — a memorized lookup table sitting
behind the name `simple_web_html_background_color`, not a parser. They are
untouched here and are their own finding.

Still RED (29): the `_draw_ir_command_index` / `_wm_material_section` /
`_draw_ir_text_command` / `_count_non_color_rect` / `partial_html` lost
spec-local helpers, the object-fit / text-decoration / font-shorthand value
mismatches, `expected software to equal opencl` (environment, classification
(c) on this host), the `#rrggbbaa` shorthand alpha case, and the array
index-assign error in the URL facade. Note also that "culls dense offscreen raw
shadows before the frame command cap" is LOAD-FLAKY: observed both PASS and
`expected 1038 to be less than 1024` on the unchanged tree.

### original diagnosis

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

## Divergence-delta step-over record (required by `.claude/rules/vcs.md`)

`sh scripts/check/check-test-tree-divergence-delta.shs origin/main HEAD` →
`PASS — 3209 pre-existing offender(s), 0 introduced by this range` (exit 0),
recorded here as the rule requires rather than stepped over silently.

The underlying guard is honestly RED on `main` and was before this branch
existed: `check-test-tree-divergence: FAIL — 3943 diverged vs 965 baselined
(3081 new, 103 fixed-but-still-baselined); 26 mirror-only (25 unallowlisted, 0
stale-allowlist)`. That backlog is not this lane's to repair.

This branch touches exactly one file that has a `test/unit/` twin —
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
(twin 342 lines vs 1912; already diverged before this change, confirmed by
`cmp` on pristine `main`). The other mirror pair in lane 4's list,
`test/01_unit/browser_engine/anonymous_block_spec.spl` vs
`test/unit/browser_engine/anonymous_block_spec.spl`, is likewise already
diverged and was NOT modified. Every other spec edited here
(`backend_metal_font_spec`, `backend_vulkan_mask_plane_spec`,
`backend_vulkan_image_exact_scratch_spec`, `draw_ir_adv_spec`) exists only
under `test/01_unit/` and has no twin.

## Chrome catalog pixel gate (2026-09-12, this lane)

`check-chrome-catalog-pixel-diff.shs` was run twice on the same host with the
same `SIMPLE_BIN`: once with the three renderer files reverted to `origin/main`
(full mode, which also re-captured the Chrome side, since this worktree carried
no `*.chrome.png`), once with them restored (`--simple-only`, reusing those
captures). Per-page `mismatch_pct` is IDENTICAL on all eight pages:

| page | before | after |
|---|---|---|
| overview | 3.89 | 3.89 |
| html | 17.11 | 17.11 |
| css-layout | 10.29 | 10.29 |
| css-paint | 10.50 | 10.50 |
| forms-media | 8.11 | 8.11 |
| animation | 15.63 | 15.63 |
| evidence | 2.26 | 2.26 |
| tab-bar | 1.14 | 1.14 |

`PASS — 8 page(s) compared, worst=17.11` both times. No page regressed, and none
improved either: the catalog pages carry no named/`hsl()` color and no
semi-transparent canvas background, so none of the three fixes is exercised
there. The gate proves absence of collateral damage, not the fixes.

Operational note for the next lane: the gate cannot find `bin/simple` from a
worktree — pass `SIMPLE_BIN`. Each full run costs 20-30 min under concurrent
load, and Chrome hits its 90 s per-page alarm on every page while still
producing a usable screenshot.
