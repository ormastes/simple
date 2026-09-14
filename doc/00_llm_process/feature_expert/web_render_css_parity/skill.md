# Web Render CSS Parity Feature Expert

## Role

Own feature-specific process knowledge for pushing the pure-Simple Web software
layout/paint engine toward pixel parity with real Chromium/Electron on the
themed widget shells (glass-vibrancy WM CSS from `generate_css`). The active
target is the cross-engine widget-shell gate:
`scripts/check/check-widget-shells-crossengine-evidence.shs`, whose pass bar is
Simple-vs-real non-text agreement >= 80% (per-channel tol 8, glyph pixels
excluded via the Chrome DOM text mask). This is a *visual-fidelity* feature area
distinct from the WM-drawing regression gate (`wm_gui_window_drawing`), which is
a consumer of the same renderer.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Renderer (owned by the browser_engine layer, consumed here):
  [src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl](../../../../src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl)
  — `parse_html` -> `extract_css`/`compute_styles` (CSS cascade) -> `layout`
  (block/flex) -> `paint` (boxes+gradients+borders+shadow+text) ->
  `simple_web_layout_render_html_software_pixels`.
- Layer expert: [doc/00_llm_process/layer_expert/browser_engine/skill.md](../../layer_expert/browser_engine/skill.md)
- CSS under test (the exact glass tokens the fixtures embed):
  `generate_css(theme)` in [src/app/ui.web/html.spl](../../../../src/app/ui.web/html.spl)
  (light theme: bg `#ffffff`, panel `#f5f5f5`, accent `#0066cc`; `.widget-panel`
  = translucent linear-gradient over `#f5f5f5` + 6-layer soft box-shadow +
  `backdrop-filter: blur(20px) saturate(180%) brightness(1.1)`; `body` =
  3 radial-gradients + a linear-gradient; taskbar-root pill = `.widget-panel`
  with 20px radius).
- Fixture builder: [src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl](../../../../src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl)
  — `gui_window_widget_html()` (320x200: column[title label, panel[status,
  Run, Save]]) and `taskbar_shell_widget_html()` (480x64: root pill ->
  panel-content -> {pinned, running, tray} nested `.widget-panel`s -> buttons).
- Gate script: [scripts/check/check-widget-shells-crossengine-evidence.shs](../../../../scripts/check/check-widget-shells-crossengine-evidence.shs)
- Comparator (OFF-LIMITS for weakening): [scripts/check/compare-widget-crossengine.js](../../../../scripts/check/compare-widget-crossengine.js)
  — loads 3 ARGB-u32 JSONs + Chrome DOM geometry, builds the text mask, and
  emits non-text agreement %, theme color counts, and pixel-derived panel band
  top/bottom. Only emits metrics; the `.shs` applies thresholds.
- Inner-loop artifacts: `build/widget_shells_crossengine/` — saved
  `chrome_*`/`electron_*` captures + `*-argb.json`, plus
  `simple_widget_crossengine_driver.spl` (renders both Simple lanes) and
  `simple_taskbar_only_driver.spl` (taskbar only, faster).
- Bug/residual tracker: [doc/08_tracking/bug/simple_web_widget_css_divergence_vs_chromium_2026-07-03.md](../../../../doc/08_tracking/bug/simple_web_widget_css_divergence_vs_chromium_2026-07-03.md)

## Measured Residual Analysis (2026-07-03, per-region, tol 8)

Current gate: window Simple/Chrome = **62.40%**, taskbar = **30.37%** (need >= 80%).
Chrome<->Electron ~99.9% (the HTML/CSS is valid; the gap is Simple's paint).
Per-pixel disagreement was mapped by masking the Chrome DOM text rects and
histogramming Simple-vs-Chrome mismatches by row band and color:

- **Window (320x200), 12214/32486 non-text px disagree.** Dominant bands:
  - Top body band y0-13 (~4100 px, full-width): Simple paints a symmetric
    dark-in-middle ramp (~218-240) that is ~10 units too dark and NEUTRAL;
    Chrome is brighter (230-247) with a BLUE tint on the top-right (accent
    radial-gradient). Missing: radial-gradient body tint (residual #2).
  - Internal band y62-71 (~2500 px): Simple ~11 too dark + no blue tint (nested
    panel / divider region).
  - Nested content interior y~100: Simple pure white 255 vs Chrome 246 (diff 9,
    just over tol) — the translucent-gradient + backdrop-filter panel tint
    (residual #1) is not applied to this nested box.
  - Bottom y168-171: 4px panel-band offset (Simple stretches panel to y167,
    Chrome content-sizes to y171) + a SPURIOUS wide light-blue (106,164,223)
    bar at y169 where Chrome is gray 239 (accent overpaint mis-placement).
  - Window is already near its measured flat ceiling (~63%); further gains need
    the soft/gradient/backdrop tones.
- **Taskbar (480x64), 11535/16565 non-text px disagree (the anomaly).** Bands:
  - Top body band y0-13 (~6000 px = 36% of non-text): same as window — Simple
    ramp ~10-15 too dark + neutral; Chrome bright + blue top-right. THIS is the
    single biggest lever; fixing the body tint could roughly halve the taskbar
    gap.
  - Pill-top y16-30: Simple grays ~12 too dark.
  - Button pills y46-63: Simple accent (106,164,223) is far too light; Chrome
    (41,126,212). The white gradient-over-accent composites ~2x too much white
    (accent count Simple 556 vs Chrome 72 on the taskbar). A localized,
    high-value fidelity fix.

## Constraints / Gotchas (READ before editing)

- **Render cost: the O(n^2) CSS-parse blocker is FIXED (2026-07-03).** A window
  320x200 render dropped from ~40 min to **~85 s** on `gui/debug/simple` (28x);
  see the browser_engine layer skill for the root cause (`char_at`/`substring`
  are O(n) in the interpreter, so `find_from`/`css_matching_close` and the nested
  `count_css_rules`/`extract_css` scan were O(n^2), traversing the ~290 KB sheet
  ~85x). Fix = native `index_of`-based `find_from` + a one-time `css.bytes()`
  array scanned by a SINGLE brace-depth pass. Node bitmap lane stayed bit-exact.
  Inner loop is now practical on the seed. NOTE: the FULL gate uses self-hosted
  `bin/simple`, where extract_css is ~3x the seed (~168 s/render); a full
  window+taskbar gate run is ~355 s isolated (< the 600 s per-render timeout) but
  will TIME OUT if another agent is saturating the host (seen once). Run the gate
  when the box is quiet, or profile via the seed for the inner loop.
- **HARD compat: node bitmap lane must stay bit-exact.** After every renderer
  edit run `JS_RENDER_RUNTIME=node sh scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs`
  (`mismatch_count=0`). The pinned node scenes use NO backdrop-filter and NO
  radial-gradient, so any NEW paint path gated on `background contains
  "radial-gradient("` or on a `backdrop-filter` declaration is safe BY
  CONSTRUCTION — it never executes for the pinned scenes. Prefer such gated
  additive paths over touching shared gradient/shadow compositing (which the
  pinned scenes DO exercise and would regress).
- Also run `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs` and
  `scripts/check/check-engine2d-nomirror-fast-render-evidence.shs` at the end.
- **Inner loop:** render just the Simple lane and run the comparator directly
  against the saved `chrome/electron` captures in
  `build/widget_shells_crossengine/`; only run the full gate for final
  confirmation. Env: `SIMPLE_EXECUTION_MODE=interpret SIMPLE_EXECUTION_LIMIT=0
  OSTYPE=darwin SIMPLE_ONE_CALL_READBACK=1`; driver binary
  `src/compiler_rust/target/gui/debug/simple`.
- **Concurrent-session clobbering is real.** The renderer file is edited by
  multiple agent sessions; back up every edit and re-verify content survived
  (a mid-session reconcile silently reverted `parse_font_shorthand_size_px`
  once during this work). Never leave the file mid-edit before a render.
- **Body background is skipped when a widget-panel is present.** In `paint`,
  `skip_widget_page_bg = has_widget_panel and (tag==html or body)`, so the
  `<body>`'s radial+linear gradient is NOT painted for these fixtures. Any
  radial-gradient body-tint fix must account for this (paint the tint on the
  page/root fill, or lift the skip for the top/bottom body bands) or it will
  have no effect.

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area, add or refresh the
links and residual metrics here BEFORE committing, so the next agent starts from
the current measured state.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`

## 2026-09-05: Vulkan 4K showcase hardening is active

The active lane is `.spipe/web_renderer_vulkan_4k_showcase_hardening/state.md`.
The canonical source runner and seven-tab page are being repaired above the
existing HTML/CSS -> Draw IR -> Engine2D contract. Two hot-path fixes are in
scope: linear preallocated tile-op construction and bounded Draw IR route-cache
keys. Do not promote current lexical HTML/CSS fixture occurrence as production
renderability, or synthetic Chrome timing as comparison evidence. The current
admitted compiler lacks a full `test`/`check` CLI and its unscoped compile path
hit ~1.69 GiB RSS; use only bounded explicit entry-closure commands and retain
the compiler blocker separately from runtime 4K measurements.

## 2026-07-05: window fixture 97.11% — the ceiling was a byte/char slice bug

- **Always suspect infrastructure before compositing math.** The documented
  54-58% "flat ceiling" was an artifact: one multi-byte char (`content: '✓'`)
  shifted every char-indexed `substring` slice after it in `extract_css`'s
  byte-offset scanner, killing ~1400/1595 rules (all WM chrome + every @media
  block). Byte scanners in this renderer must mirror byte positions with char
  positions (continuation bytes 128..191 don't advance the char counter); see
  `_cb_chars_between` and the chp mirror in `extract_css_vw`.
- `extract_css_vw(html, viewport_w)` evaluates @media (min/max-width; unknown
  feature terms fail closed, matching Chrome headless). The mobile
  `@media (max-width: 599px)` block is load-bearing for 320px fixtures.
- Interaction pseudo-classes (`:hover`, `:disabled`, ...) must never match in
  a static render — `_is_interaction_state_pseudo` in `simple_match`.
- Soft shadows: `fb_soft_box_shadow` uses per-axis gaussian CDF (`_phi256`,
  sigma=blur/2) — the exact separable model for a gaussian-blurred rect.
- Body radial tints: `Style.bg_layers_raw` + `fb_background_radial_stack_clip`.
- Iteration loop: seed `gui/debug/simple` + traced entry
  (`simple_web_layout_render_html_software_pixels_traced` prints per-stage ms)
  + PPM dump (JSON pixel dumps via interpreted StringBuilder are O(n^2)-slow);
  compare against saved Chrome ARGB with scratchpad an3.js. Full loop ~2.5 min.
- Minimal-doc bisect beats full-sheet debugging — but slice whole top-level
  blocks; truncated CSS chunks swallow appended probe rules (depth desync)
  and produce false positives.

## 2026-07-05 (final): GATE GREEN — window 97.17%, taskbar 92.37%
`check-widget-shells-crossengine-evidence.shs` passes end-to-end (exit 0,
comparator and thresholds untouched, metal backend both fixtures, panel bands
within 1px of Chrome). Closing fixes after the UTF-8/media/pseudo/shadow set:
flex min-content floor (min-width:auto), explicit CSS min-width floor on all
flex sizing branches (sections' min-width:180px overflow the row like
Chromium), and per-row gradient painting that carries the full rect geometry
so border-radius corners on gradient backgrounds render round (square accent
corners were the last panel-band-bottom miss). Remaining residuals are glyph
metrics (bitmap vs Inter), excluded by design via the Chrome DOM text mask.

## 2026-07-07: backend-isolation Gap B landed — `--web-engine` facade selector

`BrowserBackend.create(w, h, backend, web_engine = "pure_simple")` and
`cli_browser` now accept `--web-engine <name>` / `--web-engine=<name>`
(space and equals forms both parsed), threading engine selection through
`web_render_backend(name, w, h)` — the shared facade this parity work
already exercises via `simple_web_render_html_to_pixels_with_engine2d_backend`.
Default (`pure_simple`) keeps the cache-first `WebRenderPixelArtifactCache`
path byte-identical (perf anchor unaffected); `chromium` tags provenance as
`compatibility_renderer`/`chromium` and never silently substitutes
`pure_simple` pixels; unknown names loud-fail (`Err`) at construction.

**Caveat (interpret mode):** the `chromium` lane's first render call crashes
with `error[E1002] function 'web_backend_env_get' not found` under
`SIMPLE_EXECUTION_MODE=interpret` — a pre-existing interpreter module-alias
resolution gap (`mod_stub -> env_ops` re-export chain), reproduced
facade-only with zero browser code. Chromium rendering is native/compiled-
mode only until that alias-resolution gap is fixed. See
`doc/08_tracking/bug/web_backend_env_get_alias_unresolved_interpret_2026-07-07.md`
and the honest-contract pin at
`test/03_system/gui/ui_browser/backend_isolation_chromium_env_get_gap_b_spec.spl`.

## 2026-07-07: `parse_html` rewritten to a linear native-split event scanner (24x @3000)

`parse_html` no longer drives per-position `text.substring(pos, ...)` (O(offset) runtime cost →
quadratic parse, see `doc/08_tracking/bug/text_substring_o_offset_parse_html_quadratic_2026-07-07.md`);
it now builds one event stream via a single native `html.split("<")` (`_html_scan_events`) and
consumes it in a two-pass `parse_html`. 27.3s→1.1s at N=3000 (~24x), confirmed linear
(2.02–2.03x per doubling) to N=6000, 23/23 semantic fixtures byte-identical (opus-reviewed).
**Idiom lesson:** a byte-array (`[i64]`/`[u8]`) rewrite of the same function was measured **~10x
worse** under the interpreter — per-element array-index reads dominate there. Prefer one native
`split()`/`find()` call over short segments, not a byte-array walk, for interpreted hot loops in
this codebase (see also the now-dead `css_bytes_*` helpers,
`doc/08_tracking/bug/css_bytes_helpers_dead_code_2026-07-07.md`, which embody the losing idiom).
`compute_styles`'s own residual superlinearity is unrelated and still open (selector-match chain,
not parse-side).

## 2026-08-08: negative vertical margins were silently zeroed, and collapsing used plain max()

Two compounding defects in adjacent-sibling vertical margin handling
(`simple_web_html_layout_renderer_layout.spl` /
`simple_web_html_layout_renderer_foundation.spl`):

1. `margin_token_vh_px()` fed the raw CSS token straight into `parse_int()`,
   which only accumulates decimal digits and silently drops a leading `-`
   (`"-10px"` parsed as `10`). `resolve_vertical_margin_px()` then additionally
   clamped any surviving negative value in the `-999..-1` range to `0` — that
   range only looked like dead space because `parse_int()` could never itself
   produce a negative number, so nothing there distinguished "unset" from "a
   genuine negative px margin". Net effect: `margin-top: -10px` / `margin-bottom:
   -10px` behaved as `0` end-to-end.
2. Even with the sign preserved, the block-flow collapse at three call sites
   inlined a plain `max()` (`if a > b: a else: b`) instead of CSS 2.2 §8.3.1's
   `max(positive margins) + min(negative margins)`. A correct, already-written
   but until-now-unused pure helper existed for this exact formula:
   `collapse_margins_signed()` in `layout_m14_types.spl` — now wired in at all
   three sites (`display:contents` children, the main block-flow loop, and the
   `body`-top-margin special case).

Regression spec: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_margin_collapse_negative_spec.spl`.

**Verification gotcha:** `simple_web_layout_debug_layout_by_id` must be
imported via `use std.gc_async_mut.gpu.browser_engine....` — the `use
lib.gc_async_mut...` alias path (used by the pre-existing
`simple_web_flex_grow_weighted_spec.spl`) currently fails under both `bin/simple
test` and `bin/simple run` with `semantic: variable '_web_budget_clock' not
found` (a module-level `var` initializer not resolving through that import
alias in the deployed seed binary). Reproduced standalone with zero browser
code via a one-line probe; not something this change caused or could fix
(interpreter/module-loading issue, out of CSS/layout scope). File a bug if this
blocks other browser_engine spec work: the `lib.` alias path is otherwise
documented as preferred for app code, but for this module tree `std.` is the
only alias that currently loads cleanly.

## Round 3 (2026-09-12) — grid `repeat()`/`minmax()`, flex-wrap grow, inline content area

Three layout defects closed against a Chrome oracle, each with a pinned spec and
a sabotage triple. Read the bug records before touching the same code:

- `doc/08_tracking/bug/web_grid_repeat_minmax_track_list_falls_through_to_block_2026-09-12.md`
  — a track list that fails to parse does NOT degrade the grid, it disables it:
  layout gates on `grid_columns.len() > 0` and falls through to block. Any future
  track-list syntax gap has this same silent shape.
- `doc/08_tracking/bug/web_flex_wrap_line_never_distributes_flex_grow_2026-09-12.md`
  — the WRAP branch of row flex is a separate implementation from the nowrap
  branch and has repeatedly been the one missing a rule. Check it explicitly.
- `doc/08_tracking/bug/web_inline_box_takes_line_height_not_content_area_2026-09-12.md`
  — `line-height` sizes the LINE box; the inline box is the font content area,
  half-leaded. Wrapped runs are excluded because this renderer still models a
  wrapped `#text` as one tall box rather than N line boxes.

**Measurement gotchas that cost a whole pass here:**

1. Run `check-chrome-layout-geometry-diff.shs` with `GEOM_DIFF_HEIGHT=20000`.
   At the default 760 px the Draw IR viewport clip means the differ only sees
   ~6 % of a long page (158 elements across 8 pages, against 1257), and any
   ranking derived from it is unrepresentative.
2. In a git worktree, `check-chrome-catalog-pixel-diff.shs` needs an explicit
   `SIMPLE_BIN=` — a worktree carries no `build/` and it answers
   `ERROR — nothing was checked` otherwise.
3. The differ's own key scheme was wrong (it numbered `::marker` boxes as
   elements). After fixing it, mismatch counts are NOT comparable across the
   change; the round-3 metrics table carries a third column measured with the
   corrected differ over the OLD layout code for exactly this reason.
4. On long pages the mismatch COUNT saturates near 97 % because one early
   block-flow error cascades through every sibling below and the `inherited`
   filter only catches parent-repeat. Track the sum of `|dx|+|dy|+|dw|+|dh|`
   over root rows instead; that is what moves.

Current metrics: `doc/10_metrics/ui/chrome_vs_simple_catalog_diff_macos_2026-09-12.md`
§ Round 3. Largest remaining defect: block auto-height inside `<li>` (an inline
run before a nested `<p>` takes 2-3 line-heights where Chrome takes 1).

## Round 6B (2026-09-13) — bottom-margin collapse-through

`LayoutResult.trailing_margin_b` carries the margin that CSS 2.2 §8.3.1 lets
escape a block whose last in-flow child's bottom margin has nothing to collapse
against (`block_bottom_margin_collapses_through`,
`simple_web_html_layout_renderer_layout.spl`). The block's height loses it; the
parent puts it back between the block and the next sibling. Chrome's `<li>` in
the round-4 probe goes 80 -> 64 px, `<ul>` to Chrome's 104.

Three exclusions were NOT obvious and each cost a probe:
- **flex and grid ITEMS** are independent formatting contexts — check the
  PARENT's `display`, not the item's own, via `nodes[i].parent`. Letting the
  margin escape also shrinks the containing flex row by the same 16 px, and no
  catalog page catches it.
- a **self-collapsing** child must still forward its own trailing margin; the
  self-collapsing branch folded only the child's declared margins.
- **table cells need no guard** — `display: table-cell` already fails the
  display test. A cell branch was written, proved dead by sabotage, and
  deleted. Sabotage every guard you add; two of six were dead or wrong.

**Symmetric TOP-margin case is still open** and is the next real lever:
`doc/08_tracking/bug/web_first_child_top_margin_never_collapses_through_2026-09-13.md`.
It cannot use this shape — the parent is placed before the first child is
measured — so it needs `offset_layout_subtree` re-placement or a pre-pass.

**5th measurement gotcha:** the geometry differ's nth-paths desync on `html`
after `path:0/0/4/3` because Simple attributes `<li>` boxes to the `<section>`
rather than the `<ul>`; the 247/79/492 mismatch counts are one structural
divergence cascading, not hundreds of defects. Rank pages with the PIXEL
differ and trust the geometry report only above the first desync.
`doc/08_tracking/bug/web_geometry_differ_li_reparented_desyncs_nth_paths_2026-09-13.md`

## Round 7 (2026-09-13) — the TOP half landed; the shape that made it possible

The symmetric top-margin case above is now CLOSED, and it did **not** need the
pre-pass the round-6 note predicted. `LayoutResult` gained `leading_margin_t`
(the exact mirror of `trailing_margin_b`) and the block child loop does a
**two-phase correction** with the `offset_layout_subtree` that was already in
the file: place the child from its DECLARED margin-top, then re-offset the whole
child subtree by the difference against its EFFECTIVE one,
`collapse(declared, child.leading_margin_t)`. The effective value is only
knowable after the child is laid out, which is exactly the objection — the
answer is to move the box afterwards, not to measure it beforehand.

Three things that cost a probe each, all now pinned as AC in
`test/01_unit/browser_engine/first_child_top_margin_collapse_spec.spl`:
- **`<li>` is the case the catalog actually exercises** (the feature-inventory
  pages carry ~100 each) and it has a `::marker` as its FIRST node. Check that
  the marker does not consume `child_count == 0` before the escape test, or the
  fix silently does nothing on every list. AC-9.
- **Out-of-flow first children** must not donate a margin to the block. AC-10.
- **Nesting must yield ONE margin, not one per level** — the recursion is in
  returning the escaped margin upward, not in adding it at each level. AC-8.

The exclusion set was deliberately copied from
`block_bottom_margin_collapses_through` INCLUDING the height clamps, even though
CSS does let a top margin escape a fixed-height block. Widening it would move
boxes the trailing half still holds; the remaining case is recorded, not guessed.

**`::marker` bites the key scheme too, in a second place.** The 2026-09-12 fix
corrected the geometry differ's `_layout_tag`; the renderer's own
`_simple_web_layout_element` still counted markers, so every hit-test and
animation target key inside an `<li>` was off by one ordinal. All three copies
of the scheme (Chrome walker, differ, renderer) now exclude `::`-prefixed tags.
If you touch one, grep for the other two.

**6th measurement gotcha (macOS):** the PIXEL differ is impractically slow here
— one `html` page did not finish rendering the Simple side in 20 minutes, and
Chrome itself hits the 90 s screenshot alarm on every page. Budget the geometry
differ instead, and never A/B across two trees: check the two
`browser_engine/*.spl` files out at `HEAD~1` in the SAME worktree for the before
side (`.claude/rules/testing.md` § Measurement traps).

**Selector matching is pre-parsed now (round 9, 2026-09-13).** Every selector
part is parsed ONCE into a `ParsedSel` record on `RuleBuckets.parsed_groups`,
where `build_rule_buckets` runs; the per-node path
(`simple_match_parsed` / `_pseudo_ctx_matches_parsed` /
`selector_group_matches_node_parsed`) never touches selector TEXT. The text
functions (`simple_match`, `_pseudo_ctx_matches`,
`selector_group_matches_node_parts`) are retained and are exercised ONLY by the
equivalence oracle — **if you change selector semantics you must change BOTH
sides**, or
`test/01_unit/browser_engine/web_selector_parsed_equivalence_spec.spl` fails.
That spec is the contract: 177,949 comparisons over the 8 catalog pages plus an
adversarial fixture, both paths, per node.

**The trap that spec exists for:** the catalog stylesheets contain only **25
distinct selectors**, so catalog-only coverage proves almost nothing about
selector semantics. The adversarial fixture caught a real behaviour change on
its first run — `:disabled` never matches in the text path on EITHER branch
(both the `_is_interaction_state_pseudo` arm and the catch-all arm return
false), so "fixing" it to match a disabled element is a semantic change, not a
refactor. Add new selector shapes to the adversarial fixture, not to a catalog
page. Measurements: `doc/10_metrics/ui/web_perf_round9_2026-09-13.md`.

## Font faces: the generic families are resolved by the HOST (round 11)

The catalog declares nothing but `font: 16px/1.5 sans-serif` plus the UA
monospace for `<code>`, and `lang="en"`. Chrome therefore resolved those
generics with the host's own defaults — on macOS **Helvetica** and **Menlo** —
so any advance-width comparison against the bundled Noto faces is comparing two
different typefaces. Ground truth at 16 px: Menlo `M` = 1233/2048 em =
**9.633 px** (exactly Chrome's measured 9.63), Helvetica regular-to-bold
`abcdefg` = **+4.4 px** (exactly Chrome's +4).

Three traps, all of which cost a round each:

1. **`FontRasterizer.load_selected` is a PATH ALLOWLIST, not a format check**
   (`spl_fonts.spl`). A path with no entry in the pinned registry is refused
   before the file is opened. Round 9 read that rejection as "macOS TTFs are
   malformed"; nothing about the file was ever inspected. The unmanaged lane
   beside it (`load_unmanaged`) is the way in — and it must REFUSE a
   registry-owned path, or it becomes a bypass for asset-root enforcement.
2. **`ttcf` is a real format gap.** `parse_offset_table` admits `1.0`, `OTTO`,
   `true` and `typ1` — never `ttcf` — and Menlo/Helvetica ship only as
   collections. A collection face's table offsets are absolute from the FILE
   start, so slicing produces garbage; `sfnt_ttc_extract_face` repacks a face
   into a standalone blob instead, which is why glyf/cmap/hmtx and the atlas
   composite needed no change at all.
3. **The language/category coverage matrix silently replaces the family.**
   Under any `lang` other than `und` it substitutes its witness family and the
   bundled lookup then answers with that asset ALONE — which discards both an
   explicit `@font-face` source and the platform face. Face routing that works
   under `und` can be completely dead on every real page. Always probe with the
   page's actual `lang`.

Also: `resolved_font_advances` is `[i32]`, one integer per codepoint, so a
per-char 9.633 rounds to 10 and eight of them give 80 where Chrome accumulates
fractionally to 77. A face swap cannot fix that; the contained fix is to emit
`round(cum[i+1]) − round(cum[i])` from milli-px advances inside
`measure_text_advances`. Measurements:
`doc/10_metrics/ui/web_chrome_parity_round11_2026-09-13.md`.
## Round 13 (2026-09-13) — batched glyph advances, and the first layout profile

`sfnt_glyph_advance_into` re-parsed the sfnt offset table plus three
`find_table` directory scans **per glyph** (228 calls, ~1.09 ms each). It is
replaced on the hot path by `sfnt_blob_glyph_advances_into`, which does that
setup once for a whole glyph-id array, and by an `_advw` warm table in
`font_renderer.spl` keyed `(loaded-face identity, font_size)` — the same key
granularity the per-glyph path uses, because an advance is size-dependent.
Measured 228/228 batch hits, `gadv_sfnt` 351 ms -> 0, `gadv_batch` ~27 ms.
**The exactness argument is structural, not empirical**: the batch reproduces
every guard of the per-glyph function, including `_hmtx`'s left-side-bearing
bounds test that neither function reads — drop it and the batch would answer a
number where the per-glyph path answered "fail", changing glyph positions.
Oracle: `test/01_unit/lib/common/encoding/sfnt_batch_glyph_advances_equivalence_spec.spl`
(sabotage-checked).

`layout()` now has timers for the first time — `web_layout_counters_report()`,
nine buckets, same `SIMPLE_WEB_STYLE_COUNTERS=1` gate. **They are INCLUSIVE and
are not a partition**: `lay_cps` nests inside `lay_inline`; wrap/flex/table
contain `lay_measure`.

**The landmine this round added to the index:** `inline_text_advance_width`
spends 60% of its time in one `text_codepoints` decode, which *looks* exactly
like a repeat-computation. It is not — a two-entry exact memo measured **3 hits
/ 1,454 misses** on the real catalog. Do not "obviously" cache it; the 1,457
calls are 1,454 distinct strings. The real fix is to avoid building the array
when only its LENGTH is used, which needs a malformed-UTF-8 equivalence fixture
first. Measurements: `doc/10_metrics/ui/web_perf_round13_2026-09-13.md`.

**Round 13 addendum — the landmine the round itself stepped on.** The parity
lane's sub-pixel change gave `sfnt_glyph_advance_into` TWO advance fields:
`meta[2]` (rounded pixels) and `meta[18]` (milli-pixels), and the renderer's
index lane prefers `meta[18]`. They are rounded INDEPENDENTLY from the
unrounded scale, so `meta[18] / 1000 != meta[2]`. A batch replacement that
carried only `meta[2]` passed a `meta[2]`-only equivalence spec, reported zero
mismatches under a live per-call probe, and still moved all eight catalog
digests — because it was right about the field nobody reads. **If you touch an
advance path, check BOTH fields; a one-lane oracle for a two-lane function is
not an oracle.** Only the Draw IR digest gate caught it.

## Round 13 (2026-09-14): the differ was fail-open, and kerning was never read

Two independent findings. Read both before trusting ANY compared/mismatched
number recorded in rounds 11-13.

### 1. The measurement lane could report a page it never laid out

The runner binary (`build/cargo-r2/release/simple`, built Sep 12) predated
commit `08770cc5025` (Sep 14), which added the extern
`rt_engine2d_blend_cov_span_u32` — declaration in
`simple_web_html_layout_renderer_paint_primitives.spl` AND registration in
`interpreter_extern/simd.rs`, same commit. An unregistered extern answers
**silent nil**, so the layout module emitted 432 boxes on `html` of which
**432 were (0,0,0,0)** — every KEY still present, `missing_in_simple` 0, and
the differ reporting 430 "mismatches" whose delta is **Chrome's own (x,y,w,h)
verbatim**, because it is subtracting from zero.

On the tree before that commit the same differ over the same Chrome harvest
gives **html 329** with ordinary small deltas. **There was never a layout
regression to bisect**; round 12's "host/Chrome variance" (html 338 vs 430,
same commit) is the same artifact. Env vars were ruled OUT, not in — the
all-zero count is identical with and without
`SIMPLE_EXECUTION_MODE=interpreter` / `SIMPLE_TIMEOUT_SECONDS=0`.

Fixed where it can be: the differ refuses to diff an all-zero Simple side
(`all_boxes_degenerate`, fifth fatal selftest fixture, `--selftest` now
`PASS — 5 fixture(s) checked`), and caught this live on first contact.
Record: `doc/08_tracking/bug/web_html_page_zero_geometry_boxes_2026-09-13.md`.

**Two lessons to carry.** (a) A differ that compares two element lists cannot
tell "everything is wrong" from "one side never ran" — give any such tool a
non-vacuity check on the side it does not own. (b) **Always check the runner
binary's mtime against the tree you are measuring** before believing a parity
number; `src/lib` is read as source every run, but the EXTERNS it declares are
baked into the binary.

### 2. `path:(body)` is benign — it is NOT a key desync

Every page reports `missing in Chrome (Simple-only boxes): 1 — path:(body)`.
Simple emits a box for `<body>` (key `path:`); Chrome's `--dump-dom` harvest
carries no `|body|` row. Keys are matched by STRING, not by position, so one
extra box cannot shift any nth-path. `overview` proves it: 18 compared, 5
mismatched, every neighbour exact. Do not spend a round on it.

### 3. Kerning: `kern` is now read on the unmanaged lane

`FontRasterizer.load_unmanaged` builds the rasterizer with `kern_fp: 0`, so
`horizontal_kern` answered **0 for every pair on every macOS system face**,
while Chrome kerns by default. `sfnt_ttc_extract_face` copies every table when
it repacks a collection face, so the data was in `selected_blob` the whole time
and nothing read it.

New: `src/lib/common/encoding/sfnt_kern.spl` — legacy `kern`, both header
shapes (Apple 0x00010000 32-bit and MS 0x0000 16-bit), horizontal
non-cross-stream **format 0** only, binary search on the `(left<<16)|right`
key, values in MILLI-pixels so they fold into round 12's cumulative pen instead
of being rounded per pair. Measured on this host:

| face | table | `AV` | `To` |
|---|---|---|---|
| Helvetica.ttc#0 | `kern` 656 B, no GPOS | -151 units = **-1180** milli-px @16 | -227 = **-1773** |
| Menlo.ttc#0 | no `kern`, no GPOS | 0 | 0 |

**GPOS `PairPos` is deliberately NOT implemented** — neither face ships GPOS, so
it would be dead code. A face that kerns only through GPOS answers 0 from here,
exactly as before.

Two traps for the next round:
- **Do not assert "the pair at 2x size is 2x the value".** -151/2048 em is
  -1179.6875 milli-px at 16 and -2359.375 at 32; rounding each exact product
  gives -1180 and **-2359**, not -2360. Doubling a rounded number reintroduces
  the sum-of-rounded-parts error round 12 removed.
- **Kerning is ASCII-only** on this lane: the glyph-id table `_gid_lookup`
  covers 32..126, so a non-ASCII pair gets no kern. Stated, not hidden.

`render_text` still kerns at whole-pixel through `horizontal_kern`;
`measure_text_advances` is the milli-px path and is what layout and
`paint_layout_advance_parity` (2/2, green) consume.

Measurements: `doc/10_metrics/ui/web_chrome_parity_round13_2026-09-14.md`.

## Round 16 (2026-09-14): the text API is BYTE/CODEPOINT mixed — check the index kind first

`css-layout` and `css-paint` had not moved in nine rounds because the candidate
list (flex/grid sizing, `gap`, `box-sizing`, percentage widths) was the wrong
list. The whole cluster was ONE character: an `&mdash;`.

Read this before touching any wrap, measure or paint loop:

| call | indexed in |
|---|---|
| `text.len()`, `text.substring(a,b)`, `text.bytes()` | **BYTES** |
| `text.char_code_at(i)`, `text.char_at(i)` | **CODEPOINTS** |
| `resolved_font_advances` | one entry per **CODEPOINT** |
| `style_run_byte_advances(st, s)` | one entry per **BYTE** (0 on continuation) |

Every wrap offset in this renderer is a BYTE offset, because it is cut on with
`substring`. Two live defects came from mixing the two, and both were invisible
on ASCII:

- an arity guard comparing `resolved_font_advances.len()` (codepoints) with
  `txt.len()` (bytes) sent every non-ASCII run to the flat cells-per-line
  estimate — 12 px/char against a real ~7.8, so it wrapped ~50 % too early;
- `style_run_byte_advances` tried to spot UTF-8 continuation bytes with
  `char_code_at`, which DECODES and never answers 128..191, so the helper
  returned an empty table and was dead on exactly the runs it exists for.

`css-paint` 516 → 9 mismatched; `css-layout`'s root `dy` maximum 697 → 169 px.

Three traps this cost:
- **A count can rise while geometry improves.** `css-layout` went 337 → 378
  because the over-wide estimate had been compensating for a second defect in
  the opposite direction. Report the `dy` histogram, not just the count.
- **Fixing the guard alone changes nothing** — the helper behind it was also
  broken. If a fix provably reaches the right code path and moves no pixels,
  suspect its dependency, don't re-diagnose the symptom.
- **Isolate by CHARACTER, not by element.** The first four fixtures blamed
  `<code>`; swapping `—` for `xx` in the same run, with everything else held,
  was what actually named it.

Also measured and recorded rather than fixed: the `<body>` margin-collapse item
carried into round 16 was **not real on these pages** — Chrome's own numbers
have `body` at y=16 with the child flush to it, and every catalog page's `body`
row is `dy=0`. Verify a handed-down premise against run A before editing.

Measurements: `doc/10_metrics/ui/web_chrome_parity_round16_2026-09-14.md`;
record: `doc/08_tracking/bug/web_non_ascii_run_wrap_falls_back_to_flat_estimate_2026-09-14.md`.

## 2026-09-14 (round 17) — the handed-down cause was wrong; it was ONE space

Round 16 left "a `#text` node starting at a non-zero pen x wraps against the
FULL container width" as the dominant `css-layout` cluster. **That premise is
false, and this is the second round running in which a handed-down cause did not
survive contact with a probe** (round 16 falsified the `<body>` collapse item the
same way). The pen offset was already applied — an instrumented run of the real
page prints

```
R17INL|iw=728|inline_x=96|inline_w=635|avail=632
R17TEXT|node_w=632|full_adv=631|lines=1|txt=— partial; values=keyword-nu
```

`avail = iw − inline_x` is right there. The entire 24 px per `<li>` was the ONE
collapsible space between `</code>` and the text, which `text_trimmed` removes
unconditionally: ~4 px, deciding a 631 px run against a 632 px remainder.

The measurement that named it — and the one to copy — is a **Chrome-side
sabotage**: build the fixture three ways and let Chrome vote.

| `<li>` content | Chrome | Simple before | after |
|---|---|---|---|
| `<code>align-self</code>` + SPACE + `— partial; …` | 88 | 64 | 88 |
| same, space DELETED from the markup | **64** | 64 | 64 |
| the text alone, i.e. the space at pen 0 | 64 | 64 | 64 |

Row 2 is what proves it: delete the space and **Chrome itself** drops to 64. No
amount of reasoning about advance precision or the `<code>` element can survive
that. Row 3 is the control that stops the naive fix — at the start of a line the
space IS dropped, so it must not be charged everywhere.

Result: `css-layout` 378 → **5** mismatched. Fix is four lines in the inline
formatting path (`…_layout.spl`, before the `avail_inline` clamp): if a `#text`
child sits at a non-zero pen and its RAW `text_data` starts with white space,
advance the pen by one `resolved_space_advance` first.

Traps worth carrying forward:
- **Make the fixture faithful before trusting it.** The first attempt gave
  `<code>` a `sans-serif` family and no `<p>` child; it measured 0 mismatched and
  would have "disproved" a real defect. The real page leaves `<code>` at the UA
  monospace default (125 px, not 92).
- **Instrument the REAL page, not a reduction.** One `print` of
  `iw`/`inline_x`/`avail`/`lines` on `css-layout` answered in one run what four
  fixtures had not.
- **Let Chrome sabotage the hypothesis.** Change one character in the markup and
  re-measure the ORACLE. If Chrome doesn't move, your mechanism is wrong.

Next cluster, with the row that names it: a non-replaced `display:inline`
element is given the CONTAINER width, not its content width — `html`
`path:0/0/4/2/8/1/0` `<bdi>` is 86 px wide in Chrome and 728 in Simple
(`dw=642`), with `dh=6` alongside (line box 24 vs content area 18). Ten such
root rows on `html`, plus their inherited children.

Round 17 measurements: `doc/10_metrics/ui/web_chrome_parity_round17_2026-09-14.md`.

## Round 18 (2026-09-14) — the UA tables, not the layout algorithms

Three items, and all three root causes were **missing UA-stylesheet knowledge**,
not defective layout code. In every case the layout path that should have run
was already correct and already tested; the element simply never reached it.
That is the transferable lesson of this round.

1. **Non-replaced inline width** (`html` root rows for `bdi bdo cite data del
   dfn ins q s u`). The inline branch of `layout_with_style` already
   shrink-wraps (`intrinsic_text_width`, which adds the element's own padding
   and border) and already clamps the content area to the font height
   (`inline_content_area_height`). Ten tags were simply absent from
   `is_inline_tag` (`…_style.spl`), so they resolved to `display:block`, took
   the container width (728 against Chrome's 86) and a line box's height. Fix:
   twelve tags added to the UA table. **Derive that list from the measured
   Chrome `display=inline` set of the catalog, not from the HTML spec** — one
   `grep` over the harvested `*.geom.txt` gives it exactly.
2. **Replaced default box** (`animation` `audio`/`video`/`canvas`). Only
   `<iframe>` had the CSS 2.1 §10.3.2/§10.6.2 fallback; the rest had no sizing
   branch. Generalised the iframe branch behind `replaced_default_box_w/h`
   (300x150; `<audio controls>` 300x54 measured, not assumed).
3. **Form controls are widgets** (`forms-media`). `<input>` charged NO padding
   or border on its height (15 where 33 belongs — `box-sizing` reinterprets a
   *specified* height, so an auto-height control is content+pad+border either
   way), and `<select>`/`<textarea>` had no branch at all: the block path
   recursed into a select's `<option>`s and stacked them 153 px tall, where
   Chrome reports every option as 0x0.

### Traps and method notes

- **A failed sabotage is not a disproof until you check the sabotage applied.**
  The first `is_inline_tag` sabotage looked like the premise was false — the
  spec stayed 8/8. The `sed` pattern had simply not matched (the entry sits on
  a continuation line). `grep -c SABOTAGED` before re-running, every time.
- **Twins move together.** `layout.spl:_m14_is_inline_tag` is a second hardcoded
  inline-tag list for the M14 public API. Widening only one of the two would
  have left the twin architecture inconsistent; both carry the set now.
- **A size fix can make a ladder worse and still be right.** Giving
  `audio`/`video` their true 54/150 heights grew `animation`'s inherited `code`
  ladder from `dy=30` (Run A) to `dy=126` (Run B), because Simple stacks these as BLOCK boxes
  where Chrome puts them on one inline line box. Per-element geometry is now
  correct; the ladder is the next defect, not a regression of this one. Report
  both numbers rather than hiding either.
- **`intrinsic_text_width` is inline-only.** For a `<select>` it never reaches
  the `<option>` labels (option is `display:block`); `flex_item_max_content_width`
  does, and already includes the element's own padding and border.

### Next cluster, with the row that names it

**Replaced elements are block-level here and inline-level in Chrome.** On
`animation`, Chrome has `canvas` y=295 h=40, `audio` y=281 h=54, `video` y=185
h=150 — three bottoms all at 335, i.e. one line box with the boxes on the
baseline. Simple stacks them, so `dx`/`dy` stay wrong now that `dw`/`dh` are
right (`audio dx=249`, `video dy=134`). Note `img` is not in `is_inline_tag`
either, so the `grid_item_is_replaced` exclusion in the inline height clamp is
currently unreachable — the machinery for this already exists and has never run.

Round 18 measurements: `doc/10_metrics/ui/web_chrome_parity_round18_2026-09-14.md`.
