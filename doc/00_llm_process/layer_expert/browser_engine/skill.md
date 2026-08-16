# Browser Engine (Web Layout Renderer) Layer Expert

## Role

Own layer-specific process knowledge for the pure-Simple Web layout/paint engine
under `src/lib/gc_async_mut/gpu/browser_engine/`: the HTML->CSS->layout->pixels
software renderer that both the WM compositor lanes and the cross-engine widget
gates funnel through on Metal-capable hosts. Public contract: given HTML + width
+ height, produce an ARGB `[u32]` framebuffer that (a) matches pinned node
bitmap scenes byte-for-byte and (b) approximates real Chromium for themed glass
CSS.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Layer Links

- Source (owned):
  [src/lib/gc_async_mut/gpu/browser_engine/](../../../../src/lib/gc_async_mut/gpu/browser_engine/)
  - `simple_web_html_layout_renderer.spl` (~8.2k lines) — the whole pipeline.
  - `simple_web_renderer.spl` — engine2d/Metal presentation shim
    (`simple_web_render_html_to_pixels_with_engine2d_backend`,
    `simple_web_resolved_engine2d_backend_name`).
  - Browser text uses the shared Draw IR → Engine2D font-renderer path; do not add a private atlas compositor.
- Consuming feature experts:
  - [web_render_css_parity](../../feature_expert/web_render_css_parity/skill.md)
    (cross-engine widget parity gate).
  - [wm_gui_window_drawing](../../feature_expert/wm_gui_window_drawing/skill.md)
    (giant-glyph regression gate; consumer, not owner).
  - [rendering_inside_rendering](../../feature_expert/rendering_inside_rendering/skill.md)
    (iframe embedding is implemented INSIDE `simple_web_html_layout_renderer.spl`:
    replaced element, srcdoc, `space=separate|shared`, `WEB_IFRAME_DEPTH_CAP=3`).
- Related layer: [os_compositor](../os_compositor/skill.md).

## Public Contract / Key Entry Points

- `pub fn simple_web_layout_render_html_software_pixels(html, width, height) -> [u32]`
  (line ~8120): parse -> extract_css -> compute_styles -> layout -> `paint`.
  `fb` base is `argb(245,245,245)` in legacy widget_mode else white(255).
- `pub fn simple_web_layout_uses_legacy_widget_chrome(html) -> bool` = html
  contains `widget-panel` AND NOT `<style` — the fixtures embed `<style>`, so
  they use the REAL layout path (widget_mode = false), not the hand-drawn stub.
- `compute_styles` -> `Style` struct (one giant record; every new visual
  property needs a field added to BOTH the default constructor and the final
  builder `Style(...)` at line ~3555 — three call sites near lines 1684, 1688,
  3555 must stay field-consistent or it won't compile).
- Paint order in `paint` (line ~7528): per node, back-to-front: shadow
  (`fb_style_rounded_rect_opacity_clip` at box_shadow offset — HARD, no blur) ->
  background (`fb_style_background_opacity_clip`) -> border -> outline; then
  relative/absolute/positive-z passes repeat the same block.
- Gradient painting: `fb_style_background_opacity_clip` +
  `mix_color_vertical_centered` — VERTICAL linear only (varies with row);
  `parse_linear_gradient_color(raw, 0|1)` picks the first/last color of the
  first `linear-gradient(` layer; `parse_background_stack_base_color` picks the
  trailing plain-color layer. NO radial-gradient primitive, NO shadow blur, NO
  backdrop-filter compositing exist yet — these are the documented residuals.

## Known Constraints / Verification

- **Bit-exact pinned lane:** `JS_RENDER_RUNTIME=node sh
  scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs`
  (`mismatch_count=0`) is the non-negotiable regression guard. Also
  `check-engine2d-cpu-metal-parity-evidence.shs` and
  `check-engine2d-nomirror-fast-render-evidence.shs`. New visual features must
  be additive branches gated on properties absent from the pinned scenes
  (radial-gradient / backdrop-filter) to be safe by construction.
- **Interpreter render cost — the O(n^2) CSS-parse blocker is FIXED (2026-07-03).**
  Root cause: `rt_string_char_at`/interp `char_at` is O(index) (`chars().nth`),
  and interp `substring` materializes `chars().collect()` of the WHOLE string per
  call — so `find_from` (a char_at scan loop) and `css_matching_close` were O(n^2)
  over the ~290 KB embedded sheet, and the nested `count_css_rules`/`extract_css`
  find+match_close pattern traversed the sheet ~85x (measured 106 s just to count
  rules). Fixes, all in `simple_web_html_layout_renderer.spl`, node-lane bit-exact
  preserved (mismatch_count=0):
  - `find_from` now uses native `index_of` + one `substring(pos,len)` offset
    (O(n) per call; the sheet is ASCII == byte==char, which the whole file already
    assumes).
  - CSS structural scanning converted to a one-time `css.bytes()` array with O(1)
    indexed byte helpers (`css_bytes_find`/`_match_close`/`_first_non_ws`/
    `_trimmed_eq`); `count_css_rules` + `extract_css` are now a SINGLE linear
    brace-depth pass (emit at each rule's closing brace, document order preserved
    for cascade parity). `css_matching_close` deleted.
  - Result on `gui/debug/simple`: window 320x200 render ~40 min -> ~85 s (28x).
    Per-stage: extract_css 275 s -> ~58 s, count 106 s -> 1.4 s. On self-hosted
    `bin/simple` (what the gates use) extract_css is ~3x the seed (~168 s); a
    window+taskbar gate run is ~355 s isolated, fits the 600 s per-render timeout
    when the host is NOT contended by other agents' renders.
  - Remaining seed hotspots if more is needed: extract_css per-rule `substring`
    (~11 s; could build sel/decl from the byte slice), `_css_collect_custom_props`
    (still a find+match_close scan, ~6 s), paint (~14 s), compute_styles (~12 s).
    Never pass the big byte array into a hot helper WITHOUT confirming it stays
    cheap — array-param is COW-cheap here (verified 1770 calls = 21 ms), the
    slowness was iteration count, not copying.
- **Interpreter codegen gotchas seen in this file:** chained methods break (use
  intermediate `var`); `obj.field.push()` on an array element doesn't persist
  (flat arena of nodes keyed by parent index is used); `text.index_of(needle,
  pos)` ignores `pos` (use `find_from`); a `var x = if cond: a else: b` block
  binding can be treated as const at runtime and crash on later reassign
  (the chromed-scene flex-stretch path hits this ~line 7012/7063).
- **Concurrent editing:** multiple agent sessions edit this file; back up each
  edit and re-verify content after any pause.

## Session update 2026-07-20 (half-open hit-test bounds — SECOND engine in this directory, not the parity renderer)

- **This directory holds TWO separate browser engines — don't conflate
  them.** Everything else in this skill (public contract, paint order,
  CSS-parse perf) describes the monolithic
  `simple_web_html_layout_renderer.spl` pipeline (owned here, consumed by
  [web_render_css_parity](../../feature_expert/web_render_css_parity/skill.md)
  and `wm_gui_window_drawing`). `layout.spl` (`BeDomNode`, `BeLayoutBox`,
  `hit_test`) plus `browser_renderer.spl` (`BrowserRenderer`,
  `BeRenderResult`) are a SEPARATE, modular "Be*"-prefixed engine in the
  same `src/lib/gc_async_mut/gpu/browser_engine/` directory, consumed by
  `src/os/compositor/browser_backend.spl`, `src/os/apps/browser_sample/`,
  and `src/app/ui.chromium/engine_merge.spl` — not by the CSS-parity
  pipeline. A change to one does not imply anything about the other; check
  which engine a caller actually imports before assuming impact.
- **`_box_contains` (`layout.spl`, the Be* engine) is now half-open on the
  right/bottom edge** (`x < box.x+w`, `y < box.y+h` — was `<=`) to match
  the GUI reference convention (`common.ui.widget_hit._contains`) and the
  new shared interaction core's `HitProxy2D.contains_point`: a point on a
  shared border between two adjacent boxes now hits exactly one box, never
  both. `compositor_pick_topmost`/`layer_rects_overlap` are now exported
  from `engine2d/__init__.spl` and `engine2d/mod.spl` (previously internal
  to `compositor.spl`) so callers outside this layer can pick the topmost
  hit layer without reimplementing it. Conformance spec
  `hit_bounds_halfopen_spec.spl` (6/6) + `probe_hit_bounds_halfopen.spl`
  (6/6), both under `test/01_unit/lib/gpu/browser/`. This does NOT touch
  paint/CSS pixels — the parity gate is unaffected (see
  [web_render_css_parity](../../feature_expert/web_render_css_parity/skill.md)'s
  2026-07-20 note).
- See the new
  [interaction_input_routing](../../feature_expert/interaction_input_routing/skill.md)
  feature expert for the broader half-open-bounds standardization and the
  pointer-event/hit-test/dispatch core this fix feeds into — the Be*
  engine's own event handling has NOT adopted that core yet; this landing
  is the bounds-convention fix only.

## Update Rule

When this layer's public contract, source ownership, tests, architecture, or
verification requirements change, update this skill with the new links and
handoff notes before committing.

## Freestanding data-channel hardening (2026-07-26)

The freestanding/cranelift lanes lose arrays crossing Simple-function
boundaries (guide:
`doc/07_guide/compiler/backends/freestanding_safe_channels.md`). Landed in
this layer: the HTML scan is INLINED into `parse_html` (foundation.spl —
both a nested `[[text]]` return and a same-module global handoff lost the
event arrays; receipt `scan-handoff-loss returned=15 module=0`);
`sha256_text` is a single function (digest `[i64]` return arrived empty →
provenance `material=""`); CSS `group_parts` helpers are inlined with a
`[css-extract] degenerate` receipt; `_cpu_draw_ir_nth_int`-style scanners
bind `char_code_at` as i64 (never chain `.to_i32()`). When touching parse/
CSS/render handoffs, keep arrays local or project scalars — and keep the
receipts (each is negative-control verified).

## GPU-runnable offloadability check (2026-08-02)

This layer (plus `src/lib/gc_async_mut/gpu/engine2d`) is scanned by the
gpu-runnable transitive checker `src/app/gpu_lint/gpu_runnable_scan.spl`
(`bin/simple run` it; inventory/warning mode). Current: 1463/3146 function
names blocked, 133 overload-tainted names, 10/24 roots BLOCKED — dominant
blockers are string ops, list-push, and text interpolation on paint-reachable
paths. Before refactoring hot render code, check whether it sits on an
offload root's closure; prefer the core/shell split (pure numeric core,
host-only shell) so the core stays offloadable. Details, ban list, and the
phase-by-phase GPU-reality audit:
[gpu_offload_check feature expert](../../feature_expert/gpu_offload_check/skill.md).

## Session update 2026-08-05 (the viable probe was FAIL-OPEN against the render lane's op set)

The 2026-08-02 deep probe below tested `clear + draw_rect_filled` and nothing
else, so it did not predict the render lane it was gating. Measured on the
dual-GPU host: `auto` selected **cuda**, whose 8x8 fill round-tripped
`device_readback`, while **every real web frame on that lane returned
`source=cpu_fallback handle=0 identity=0`**. Op bisect: clear / fill /
sub-blit / full-blit / blend-blit all stayed `device_readback`; the **clipped
fill** was what flipped it, because `CudaBackend.set_clip` only mutates the CPU
mirror and the next paint then takes `_begin_cpu_path`/`_finish_cpu_path`,
latching `cpu_fallback_used` for the whole surface. Every page with text paints
under a clip. `vulkan`/`qualcomm` served the identical frame on-device and were
never reached.

`Engine2D.probe_backend_viable` now requires **fill + CLIPPED fill + draw_image
blit**, all device-proven, with four disjoint pixel witnesses (blit at (0,0),
unclipped fill at (7,7), clipped fill at (3,3), untouched at (5,0) proving the
clip clipped). Auto now names a lane whose showcase frame reads back
`host_cache_after_device_present` with real credentials, bit-identical to the
CPU ground truth.

**Rule for this layer: a resolved lane NAME is not evidence — only the readback
source is.** `resolved=<gpu>` with `source=cpu_fallback` is a routing defect.
`test/03_system/gui/web_showcase_full_gpu_offload_spec.spl` is the gate that
holds this (per-example `[showcase-lane]` receipts; a named GPU lane serving a
CPU frame is a hard `LANE INTEGRITY FAILURE`, a named CPU lane is
inconclusive-but-green). Before that fix the same spec silently retargeted all
13 examples to `"software"` and reported `13 examples, 0 failures`.

## Session update 2026-08-02 (backend auto-resolution, heuristic sizing, position:fixed, platform nil-guard)

- **Viable-probe "auto" backend resolution** (`b0ef8e6aee5` engine2d +
  `6eb19236c05` browser side): engine2d `engine.spl` "auto" now deep-probes
  each candidate (create 8x8 → clear+rect+submit+present → readback; **extended
  2026-08-05** to clear+clipped-rect+rect+blit+submit+present → readback) and
  requires device provenance plus a pixel round-trip before selecting; a
  lane that looks available but cannot render is rejected with a
  **`[backend-resolve] <name> rejected: <why>`** line (grep for that prefix
  when diagnosing lane selection) and the next candidate is tried. Result is
  memoized per process; **explicitly named backends are never silently
  swapped**. The browser shim's auto branch
  (`simple_web_engine2d_renderer` via `simple_web_renderer.spl` /
  `simple_web_resolved_engine2d_backend_name`) routes through this
  resolution.
- **Heuristic fast path fixes + one OPEN misroute:** the whitelist-of-sizes
  trap is fixed — `_first_px_dimension` now parses the declared
  `prop: <N>px` value (char_code_at, not char_at), so animated
  width/height ticks paint pixel-exact; background resolution now scans
  style-range selectors for a body rule color (`_style_body_rule_color`).
  **Open defect (fix in flight):** with an explicit GPU backend name the
  heuristic fast path still misroutes class-selector docs — don't treat a
  heuristic-path render of class-selector HTML under an explicit GPU
  backend as evidence either way until that lands.
- **`Style.position_fixed`** (`d05b29b46d0`): new field threaded through all
  Style constructors (the three field-consistent call sites noted above now
  include it), with decl parsing and a "fixed" arm in position resolution
  (was falling through to absolute/static). Same commit made the margin
  family honor CSS source order (last-declared wins per side via
  `decl_tbl_last_index` — a longhand only beats a `margin` shorthand when
  declared after it).
- **platform.spl nil-guard trap** (`30971e2f946`, both nogc tiers):
  `detect_os()`/`detect_arch()` guarded `env_get` results only with
  `!= ""` — **nil passes that guard**, so any host without OS/OSTYPE
  exported crashed `.lower()` in the interpreter on the first shallow probe
  of every "auto" resolution. Pattern to copy: `if x == nil: "" else:
  x.lower()`. Same commit gates probe `shutdown()` by
  `engine2d_shutdown_has_typed_route` (duck-typed virtual shutdown SIGILLs
  in renderer-bearing JIT units).
- Second-render corruption fixed by renaming match-arm bindings in
  `simple_web_render_session` (interpreter arm-binding leak; see
  `doc/08_tracking/bug/render_session_second_render_match_arm_shadowing_bx_2026-08-02.md`).

## Render budget is a silent-truncation hazard (2026-08-02)

This layer owns `simple_web_html_layout_renderer_foundation.spl`, which defines
the wall-clock render budget. Contract for anyone writing a spec against this
layer:

- `WEB_RENDER_BUDGET_MS = 10000` (`..._foundation.spl:81`) **trips under
  interpreter load and then silently publishes truncated styles** — no error,
  exit 0, a plausible-but-wrong render. Any parity/showcase spec that renders a
  non-trivial page on the interpreter is exposed.
- Sanctioned opt-in, called from the SPEC:
  `simple_web_layout_set_render_budget_floor_ms(900000)` — exported at
  `..._foundation.spl:176`, **raise-only** (`ms > 0`).
  Companions: `simple_web_layout_render_budget_floor_ms()` (read) and
  `simple_web_layout_restore_render_budget_floor_ms(ms)` (scoped restore,
  accepts `>= 0` so a bounded degraded-retry caller can lower back to
  "no floor"). Production precedent for the raise/restore pair:
  `simple_web_layout_engine2d_fast.spl:306`.
- A floor is a **calibration knob, not a bypass** — the budget still expires
  past the floored deadline.
- **Raising the in-tree default `WEB_RENDER_BUDGET_MS` is forbidden.** Arm the
  floor per-spec instead.
- Env override, read at `..._foundation.spl:127`: `SIMPLE_WEB_RENDER_BUDGET_MS`
  (unset/non-numeric falls back to the default).

Consumer using this today: `test/03_system/gui/web_showcase_full_gpu_offload_spec.spl`.

Seven GPU-offload lanes over this layer are green; the evidence map and the
companion `# @exec_limit` trap live in the
[gpu_offload_check feature expert](../../feature_expert/gpu_offload_check/skill.md),
with the authoritative counts in
[doc/03_plan/platform/structural_compute/webrender_gpu_offload_plan.md](../../../03_plan/platform/structural_compute/webrender_gpu_offload_plan.md).

## Caller-frame silent interpreter fallback (2026-08-06, OPEN)

The engine's wall-clock cost depends on **which module's frame calls it**,
not just args/size. `browser_engine_pixels_at(url, 64, 36)` = ~40s CPU when
called from `render_adapter.spl`'s chain, but >300s CPU (never finished an
1800s budget, 4 attempts) when called from `gui_window.spl` — a module
importing the extern/dlopen-heavy `gui_renderer`. Mechanism: JIT lowering
fails silently for that caller, and the ENTIRE callee tree (all of this
layer) runs tree-walk. No diagnostic; uniform ~10-50x slowdown from the
first log line is the signature. Detection: time the same engine call from
two caller modules — ratio >3x = fallback. Workaround pattern: hoist the
engine call into a JIT-healthy frame (e.g. the app's `main()`) and pass the
pixel buffer down as data. Full isolation matrix:
`doc/08_tracking/bug/gui_window_caller_frame_silent_interp_fallback_2026-08-06.md`.

## Coverage closure + hardening lanes (2026-08-15)

- ~40 `*_coverage_closure_spec.spl` files under `test/01_unit/browser_engine/`
  push layout/style/paint/dom modules to 100% recordable branch coverage.
  Run: `SIMPLE_COVERAGE=1 SIMPLE_TIMEOUT_SECONDS=600 bin/simple test
  --no-session-daemon <spec>` — coverage records only under that env var,
  and "recordable" excludes known collector gaps (bugs
  `coverage_collector_skips_pub_val_and_match_heads_2026-08-15.md`,
  `coverage_probe_plan_skips_struct_method_decisions_2026-08-15.md`).
- System lanes: `test/03_system/browser_engine/docker_vulkan_browser_spec.spl`
  (gates `scripts/check/check-simple-web-browser-docker-vulkan.shs`, lavapipe
  in Docker) and `chrome_vector_font_differential_spec.spl`
  (tool: `tools/vector_font_diff/`).
- Interpreter fixes that unblocked these: ClassInstance `simple` handling and
  nested field-index assignment. Feature-side handoff:
  [browser feature expert](../../feature_expert/browser/skill.md).

## Session update 2026-08-16 — `BeLayoutBox` content contract is now executable

**Read this before touching `layout_box.spl`, `layout_core.spl`, or anything
that consumes a layout box.**

`BeLayoutBox` stores the **border box** (`x`/`y`/`width`/`height`) plus the box
model and *derives* the content rectangle on every call:

    content_x      == x + padding_left + border_width
    content_y      == y + padding_top  + border_width
    content_width  == width  - padding_left - padding_right  - border_width * 2
    content_height == height - padding_top  - padding_bottom - border_width * 2

Two consequences, both of which have already produced dead code:

- `content_x`/`content_y`/`content_width`/`content_height` are **methods, not
  fields**.
- A box names its element by the integer `node_id` (`-1` for anonymous). There
  is **no** `node` field holding a `BeDomNode`, and no pipeline currently offers
  a `node_id -> BeDomNode` resolution — which is why `_paint_box` was deleted
  rather than ported (`81684d8af46`; record
  `layout_paint_paint_box_dead_code_wrong_belayoutbox_shape_2026-08-15.md`).

The contract is now stated executably by
`test/03_system/browser_engine/layout_box_content_contract_spec.spl` (plan:
`doc/03_plan/sys_test/browser_engine_layout_box_content_contract.md`; mirror:
`doc/06_spec/03_system/browser_engine/layout_box_content_contract_spec.md`).
Its third scenario mutates padding *after* construction — the only assertion
that distinguishes a derived content rectangle from a stored one, i.e. the exact
defect shape of `_paint_box`.

Also worth knowing: the engine does **not** clamp an over-constrained box.
Padding plus border wider than the box yields a negative `content_width()`;
callers must handle that rather than assume non-negative.

`_apply_opacity` is `layout_paint.spl`'s entire surface and has **zero product
callers** — only the unit coverage spec imports it, and `StyleProps` has no
`opacity` property, so there is no CSS-to-paint producer. Do not add system-tier
"integration" coverage for it without first wiring a real producer.

**Status: TEST_BLOCKED.** The spec has never been executed — no admitted
pure-Simple CLI exists in this tree (`deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`).
It is written fail-closed to verify automatically once one is available; do not
report it as passing until it has actually run.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
