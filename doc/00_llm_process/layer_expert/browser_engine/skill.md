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
  - `famous_site_glyph_compositor.spl` — glyph atlas compositor (separate path).
- Consuming feature experts:
  - [web_render_css_parity](../../feature_expert/web_render_css_parity/skill.md)
    (cross-engine widget parity gate).
  - [wm_gui_window_drawing](../../feature_expert/wm_gui_window_drawing/skill.md)
    (giant-glyph regression gate; consumer, not owner).
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

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`

## 2026-09-14 — byte vs codepoint indexing is a layer-wide hazard

The `text` primitives this layer builds on are **mixed**: `len()`, `substring()`
and `bytes()` are BYTE-indexed; `char_code_at()` and `char_at()` are
CODEPOINT-indexed. On ASCII the two coincide, so a confusion here passes every
test until one `&mdash;`, accent or `×` appears.

Wrap offsets, `wrap_starts`/`wrap_ends`, and everything downstream that cuts
with `substring` are BYTE offsets. `resolved_font_advances` is per CODEPOINT.
The bridge between them is `style_run_byte_advances` (one advance per byte, 0 on
continuation bytes) plus `utf8_encoded_len` / `next_codepoint_start`
(`simple_web_html_layout_renderer_layout.spl`). Use those; do not open-code a
UTF-8 classifier on `char_code_at` results — it cannot work, and round 16 found
exactly that mistake sitting dead in the tree since round 12.

**Round 17 closed the whole residue — the census was larger than round 16's two
named sites.** Grepping both layout files and `…_paint_primitives.spl` for the
pattern (a BYTE offset reaching `char_code_at`/`char_at`, or `txt.len()` used as
a loop bound over them) found **six** live sites, not two:

| helper | old behaviour on non-ASCII |
|---|---|
| `text_line_advance_width` | one flat advance charged per BYTE |
| `wrap_line_end` | a CHARACTER budget spent in bytes |
| `_lay_ellipsize_text_for_width_inner` | measured one char, emitted another |
| `_table_text_min_content_width` | read past the end, over-sized the column |
| `reverse_text_for_paint` | counted down from the BYTE length |
| `fb_text_sparse_range`, `fb_text_thin_scaled_clip_range` | wrong glyph, advance per byte |

All six now step by codepoint and test bytes with `bytes()`.
`resolved_text_range_width` is **gone**: the ellipsize loop was its only caller,
and once that loop reads the per-byte advance table the function is dead — a
mixed-index helper left lying around is a trap for the next reader, so it was
deleted rather than kept.

Lesson for this layer: when one instance of this mix is found, **census the
whole layer in the same pass**. Round 16 named two sites from the two it had
debugged; three of the six above were never mentioned and had been wrong just as
long. The grep that finds them all is `char_code_at\|char_at(` over the layer,
then reading each hit for what index space its bound comes from.

Records: `doc/08_tracking/bug/web_non_ascii_run_wrap_falls_back_to_flat_estimate_2026-09-14.md`;
`doc/10_metrics/ui/web_chrome_parity_round17_2026-09-14.md`.

## The UA stylesheet is a layer of this engine, and it is three hardcoded tables

Round 18 (2026-09-14) fixed three unrelated-looking geometry clusters that all
had the same shape: **the layout algorithm was right and the element never
reached it**, because the UA-stylesheet knowledge that routes it lives in
hardcoded tables that were incomplete.

Where that knowledge lives, and what each table decides:

| table | file | decides |
|---|---|---|
| `is_inline_tag` | `…_renderer_style.spl` | `display:inline` (applied at `…_declarations.spl:1269`) |
| `_m14_is_inline_tag` | `layout.spl` | the same thing for the M14 public layout API — a **twin**, widen both |
| per-tag UA branches | `…_declarations.spl` (~:1229-1420) | font, padding, border, `display` for headings, lists, form controls |
| `replaced_default_box_w/h` | `…_renderer_layout.spl` | the §10.3.2/§10.6.2 fallback box for replaced elements |
| the widget branch | `…_renderer_layout.spl` | `input`/`select`/`textarea` size and, critically, that they do NOT lay children out |

Three rules this layer earned the hard way:

1. **A missing tag reads as a layout bug.** `<bdi>` at 728 px looked like a
   shrink-to-fit defect; the shrink-to-fit code was fine and had been for
   rounds. Before reading a layout loop, print the element's resolved `display`
   and compare it with Chrome's — one probe settles which layer owns the defect.
2. **Populate these tables from measurement.** The catalog's harvested
   `*.geom.txt` carry Chrome's own `display=` for every element; a `grep` over
   them gives the real inline set. A list written from the HTML spec would have
   included `ruby`/`rt` (Chrome: `display:ruby`, not `inline`) and would have
   missed nothing useful.
3. **Some elements must RETURN before the child recursion.** A `<select>` that
   recurses stacks its `<option>`s as flow boxes and grows to 153 px; Chrome
   reports every option as 0x0 because a select renders them in a popup. The
   replaced branch and the widget branch are both "return before children"
   branches, and that is the load-bearing part of each, not the size table.

4. **Baseline rules need a TIGHTER scope than `grid_item_is_replaced`** (round
   19). That predicate covers form controls as well as media, and this engine
   gives `input`/`select` `display:inline`, so scoping CSS 2.1 §10.8.1's
   "inline replaced -> bottom margin edge" rule by it silently broke a
   `<label>`+`<select>` height (33 -> 39) with only one spec in sixteen
   noticing. Media aligns by bottom margin edge; a form control aligns by its
   INNER TEXT baseline. Use `replaced_media_bottom_edge_tag`, and remember
   Chrome reports `input`/`select`/`textarea`/`button` as `inline-block`.
   **That wrong rule scored 82 fewer mismatches on the oracle** (forms-media
   100 -> 18) and was still rejected: the input's 6 px error did not vanish, it
   moved from the `input` row to the `label` row, same magnitude opposite sign.
   The correct rule, derived from values already present, is
   `control baseline offset = pad_t + border_t + strut_baseline(control font)`
   → ascent 21, descent 12, line 33 — satisfying both the spec and the page.
   If `input` is ever flipped to `inline-block` to match the census, the
   existing `inline-block && child_count==0` arm hands it bottom-edge again;
   the form-control arm must be tested first.
5. **The geometry differ compares a boxless element against `0,0,0,0`.** Chrome
   gives `<wbr>` (and anything else that generates no box) an all-zero rect, so
   a correctly-placed `<wbr>` reads as a ~9,800 px error. One such row is 80% of
   the `html` page's whole Σ. This is an instrument convention, not a layout
   defect — fix it in the differ or report Σ both ways, never by making layout
   emit `0,0,0,0`.

Known residue this layer still carries, measured rather than assumed: a uniform
16-18 px line-box offset on `animation` below the media line (what is left of
round 19's fix); `<audio>`'s FALLBACK children are laid out here and by Chrome
are not; form controls are `inline`-displayed here and `inline-block` in Chrome;
and a text control's `size` width is measured on the 8 px bitmap cell
(`char_w = 6*glyph_scale`, 6 px at the 13 px UA form font) where Chrome uses the
face's OS/2 `avgCharWidth` (7.25) — real metrics DO resolve at 13 px (avg 6.57
over an alnum sample), so the gap is a missing metrics FIELD, not a missing
font. None of these is papered over with a fudge.

**Round 20 corrections to the paragraph above — two of its claims were wrong.**

* *"a text control's `size` width … Chrome uses the face's OS/2 `avgCharWidth`
  (7.25) … the gap is a missing metrics FIELD"* — **false**. `sfnt*.spl` parses
  no OS/2 table at all, and more decisively, Simple resolves `sans-serif` to
  **Helvetica**, whose `xAvgCharWidth` is 904/2048 = 0.4414 em = **5.89 px** at
  13.33. No macOS face yields 7.25 (SFNS 7.73, SFNSRounded 7.65). Exposing the
  field would move `size=20` from 138 to ~136 — *further* from Chrome's 163.
  The gap is **font SELECTION** for form controls, not a missing field.
* *"form controls are `inline` here and `inline-block` in Chrome"* — true, but
  the baseline rule that flip is meant to enable needs **three arms**: text
  `input` and `select` fill their line (h = the label's h, 33/35); `textarea`
  leaves 7 px below (48 in a 55 line); checkbox/radio are 13 px boxes inside an
  ordinary 24 px text line. One rule for all four puts checkbox on a 13 px line.

**This layer now distinguishes "is a layout element" from "generates a box".**
`_simple_web_layout_element` decides ORDINALS and must mirror the differ
walker's `layoutEl` byte-for-byte (`wbr` is in it). `_simple_web_generates_no_box`
decides GEOMETRY (`wbr` is out). Because the nth-path key comes from a DOM
sibling walk and never from the emitted rows, suppressing a row cannot move any
other element's path — round 19 believed the opposite and deferred a fix on it.
`<audio>`/`<video>` fallback children and `<option>` in a closed `<select>` are
still boxed here and are not by Chrome; they now surface as `extra_box` rows.

## Form controls are widget boxes with their OWN width arithmetic

The widget branch (`…_renderer_layout.spl`, `input`/`select`/`textarea`)
returns before child recursion. Its intrinsic width is NOT `columns × text
advance`: Chrome adds a fixed font-derived INTERCEPT, so `input` content =
`size*7 + 5` and `textarea` content = `cols*8 + 17` — separate arms, because
Chrome gives them different UA fonts and a textarea reserves a scrollbar
gutter. **Never use `style_char_w` (the 6 px bitmap CELL the rasteriser draws
into) as a column advance** — that was the round-21 defect, and it is a
different quantity from both the text advance and any font's `xAvgCharWidth`.
`<select>` does not use this path at all (max-content + `SELECT_ARROW_WIDTH_PX`).
Control HEIGHTS are already Chrome-correct; the open gap is control POSITION.

Records: `doc/10_metrics/ui/web_chrome_parity_round21_2026-09-14.md`;
`doc/10_metrics/ui/web_chrome_parity_round20_2026-09-14.md`;
`doc/10_metrics/ui/web_chrome_parity_round19_2026-09-14.md`;
`doc/10_metrics/ui/web_chrome_parity_round18_2026-09-14.md`;
`doc/08_tracking/bug/ifc_linebox_spec_imports_nonexistent_layout_inline_2026-09-14.md`.
