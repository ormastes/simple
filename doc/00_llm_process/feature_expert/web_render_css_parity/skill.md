(numbers pending: re-measured against Chrome 159 — see the baseline file)
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

### Round 19 — replaced MEDIA made inline-level (428 -> 429 count, animation Σ -86%)

Round 18's "next cluster" (below, now CLOSED) was real. `is_inline_tag` carried
no replaced tag at all, so every one fell through to the block path. Adding
`img svg video audio canvas iframe embed object` to it and to the M14 twin,
plus CSS 2.1 §10.8.1's bottom-margin-edge baseline, took `animation`'s Σ down
86% (3405 -> 481; `video dx=549 -> 9`, the `code` ladder `dy=126 -> 18`). SEVEN
of eight pages stayed **byte-identical**; the count went UP by one (a new row
with an identified mechanism, item 3 of "what is left").

**The headline number is deliberately not the best one produced.** An
intermediate state scored **347** — `forms-media` 100 -> 18 — and was REJECTED
as a compensating error; see the landmine below. Read
`doc/10_metrics/ui/web_chrome_parity_round19_2026-09-14.md` before quoting any
round-19 figure.

Landmines this round added to the index:

- **A better oracle number is not automatically a better tree, and the oracle
  cannot tell you.** Scoping the §10.8.1 bottom-edge rule by
  `grid_item_is_replaced` reached form controls (that predicate contains them,
  and this engine gives `input`/`select` `display:inline`) and moved 82
  `forms-media` rows. It was two wrongs cancelling: across the runs the text
  input's 6 px did not vanish, it MOVED from the `input` row to the `label` row,
  same magnitude opposite sign. The oracle preferred it; a UNIT SPEC caught it
  (`form_control_widget_box_spec` AC-6, 33 -> 39). **Run the neighbours before
  believing a large win**, and ask what the rule physically claims: bottom-edge
  puts the control's bottom on the baseline and still adds the strut descent,
  where Chrome puts the control's INNER TEXT baseline there.
- **A predicate's existing scope is not a licence to reuse it.**
  `grid_item_is_replaced` reads like the right set for a replaced-element rule.
  Use `replaced_media_bottom_edge_tag` for baseline questions.

- **Check the hand-off's premises against the oracle BEFORE reading code.**
  Three were checked, two were false. "`input` is `display:inline` in Chrome" is
  wrong twice over — Chrome reports `input`/`select`/`textarea`/`button` as
  **`inline-block`** (census: `awk -F'|' '{print $3, $8}' *.geom.txt`), and this
  engine already gives `input`/`select` `display:inline`
  (`…_declarations.spl:1394`), i.e. wrong the opposite way. And the eight-page
  catalog has **no `<img>` and no `<iframe>`** to measure a default box against.
  The census also turned up `svg` (display=inline, dx=124), which no brief named.
- **`grid_item_is_replaced` is NOT the right scope for a baseline rule.** It
  contains form controls, and because `select` is also `display:inline` here, an
  unscoped "inline replaced -> bottom margin edge" predicate silently took
  `form_control_widget_box_spec` AC-6 from 33 px to 39. Scope the §10.8.1 rule
  to replaced MEDIA (`replaced_media_bottom_edge_tag`); a form control's
  baseline is its inner text baseline.
- **The Σ metric has been lying for at least two rounds.** ONE `<wbr>` root row
  carries Σ=9963 of `html`'s 12496 — Chrome reports a boxless element as
  `0,0,0,0`, so the differ compares a real position against a reporting
  convention. `html`'s real Σ is 2533 and its real top cluster is `li` (49 of 77
  root rows, root defect at `/39`, an `hr`-in-`div`). Report Σ with and without
  `wbr`. Fixing it belongs in the differ, not in layout.
- **Control widths are measured on the 8 px bitmap cell.**
  `style_char_w -> char_w(fs) = 6 * glyph_scale(fs)`, `glyph_scale(13)=1`, so
  `size=20` yields 6 px/char where Chrome's 13.33 px UA form font gives 7.25.
  Real metrics DO resolve at 13 px (`resolve_font_metrics_with_language` -> avg
  6.57 over an alnum sample), so the gap is not a missing font — Chrome uses the
  face's OS/2 `avgCharWidth`, which this metrics surface does not expose. Expose
  it; do not multiply the cell by a constant that happens to land on 163.

### Previous cluster (round 18) — CLOSED by round 19

**Replaced elements are block-level here and inline-level in Chrome.** On
`animation`, Chrome has `canvas` y=295 h=40, `audio` y=281 h=54, `video` y=185
h=150 — three bottoms all at 335, i.e. one line box with the boxes on the
baseline. Simple stacked them, so `dx`/`dy` stayed wrong once `dw`/`dh` were
right (`audio dx=249`, `video dy=134`). `img` was not in `is_inline_tag`
either, so the `grid_item_is_replaced` exclusion in the inline height clamp was
unreachable — the machinery existed and had never run.

Round 18 measurements: `doc/10_metrics/ui/web_chrome_parity_round18_2026-09-14.md`.
Round 19 measurements: `doc/10_metrics/ui/web_chrome_parity_round19_2026-09-14.md`.

### Round 20 — the `wbr`/Σ item above is CLOSED; two hand-off premises were FALSE

**Boxless elements now compare as "no box" (`chrome_reports_no_box`,
`layout_geometry_diff.spl:95`).** Chrome's all-zero rect means *no box*, not
*position 0,0*. Rule: Chrome-boxless + Simple-boxless-or-absent = agreement;
Chrome-boxless + Simple-real-box = one `extra_box` mismatch with **deltas
zeroed**, so Σ weighs the defect, not coordinates Chrome never claimed. The
reverse directions (Simple all-zero, or Simple absent, where Chrome has a real
box) stay full-Σ mismatch / `missing_in_simple` — pinned by two control
fixtures. Landed: 429 → 428, `html` Σ 12496 → **2533**, and 5 of 8 pages
byte-identical.

- **The boxless set is a CENSUS, not a tag list — and `<br>` is NOT in it.**
  Five elements, three causes: `wbr` (html), two `<span>` fallback children of
  `<audio>`/`<video>` (animation), two `<option>` in a closed `<select>`
  (forms-media). Only `wbr` is boxless as a property of its tag. `<br>` has a
  real Chrome rect — the round-19 guess "likely br, template, head children"
  would have regressed it.
- **Round 19's reason for deferring the layout half was FALSE.** "Emitting no
  box shifts the differ's path ordinals" — it does not. The key comes from
  `_simple_web_node_target_key` → `_simple_web_element_child_ordinal`, a DOM
  sibling walk that never reads the emitted rows. Keep `wbr` in
  `_simple_web_layout_element` (ordinals — Chrome's walker counts WBR too) and
  exclude it in the NEW `_simple_web_generates_no_box` (geometry). Two
  predicates, two jobs.
- **Residual, stated:** `<wbr>` still advances the inline pen 1 px (Chrome: 0).
  Sub-tolerance, so no catalog page sees it.
- **Form-control HEIGHTS are already correct** (round 21 measurement): `input
  dh=0`, `textarea dh=0`, checkbox/radio already take the UA 13×13 box. Only
  `select` is 2 px short. The "three height arms" hand-off was aimed at a
  defect that is not there. What IS wrong is control POSITION (input `dy=6`,
  button `dy=17`, output `dx=7 dy=24`) — and checkbox/radio are **not
  vertically centred**: 4 px above / 4 px below on an 18 px inline box, which
  is `margin: 3px 3px 3px 4px` + `vertical-align: baseline`. Do not hardcode a
  centring offset; it fits one font size and no other.
- **The control-width gap is NEITHER a face gap NOR an OS/2 gap — both stories
  are dead.** Measured round 21: Chrome's computed `fontFamily` for a control
  is literally **`Arial`** (not `-apple-system`, and `SFNSText.ttf` does not
  exist on this host). **Arial's `xAvgCharWidth` is 904/2048 — the SAME as
  Helvetica's**, because Arial is metric-compatible with Helvetica by design
  (`measureText('0')` = 7.4135 in both). So Simple ALREADY loads a metrically
  identical face. `xAvgCharWidth` is not the quantity either: it gives 5.885
  where the measured slope is 7.0. **Add no OS/2 parser** — it would be unused
  code computing a number Chrome does not use.
- **The 7.25 was an artifact of dividing ONE width by its `size`**, which folds
  Chrome's fixed font-derived INTERCEPT into the slope. Fit a LINE:
  `input` content = `N*7 + 5`, `textarea` content = `N*8 + 17` (separate arms —
  different UA fonts, and textarea reserves a ~15 px scrollbar gutter). Verified
  content-box on two pages with different author padding. For `<input>` the
  slope is **font-INDEPENDENT** (Arial/Times/SF Pro all 7.0 despite different
  `'0'` advances); monospace controls DO track their `'0'` advance. Landed in
  round 21 as four constants at `…_renderer_layout.spl:699-702`.
- **Rank root rows by Σ before choosing a target.** Round 21's Σ sort found
  `css-layout`'s single positioned `span` at **Σ 1467 (26% of the whole
  catalog)** and `forms-media`'s `<p>` in a closed `<details>` at **Σ 864** —
  41% of all catalog error in two rows, neither of which any brief had named.

- **`width:auto` on a `position:absolute` box is SHRINK-TO-FIT, not "fill the
  containing block"** (CSS 2.1 §10.3.7). Filling is only for the case where BOTH
  `left` and `right` are given. `absolute_outer_width` fell through to
  `containing_w` and produced `w=810` against Chrome's 77 on the catalog's one
  absolute box — and because `absolute_child_x` resolves `right` as
  `padding_box − OUTER_WIDTH − right`, the wrong width also dragged x to 35
  against 769. **One defect, two of the four deltas.** Fixed round 22 at
  `…_renderer_layout.spl:1626`, reusing `flex_item_max_content_width` (the
  measurement `<select>` already uses — no new surface). `available` for the
  clamp is the padding box **minus whichever offset is specified**: Chrome
  clamps an overflowing box to 890 in a 900 px block, not 900. Only an
  overflowing fixture can see that, so measure it rather than assume it.
- **`dy=0, dh=0` on a huge-Σ row means the feature IS implemented** and one arm
  of the width/x resolution is missing. Read which deltas are ZERO before
  concluding a feature is absent — that is what turned "absolute positioning is
  broken" (three rounds of not looking) into a one-arm fix.
- **Chrome's `getBoundingClientRect()` is NOT a truth oracle for "is this
  rendered".** Blink force-lays-out a `content-visibility: hidden` subtree when
  script measures a descendant, so a NOT-rendered element returns a fully
  non-zero **phantom** rect where it would sit if rendered. `forms-media`'s
  closed `<details>` reported `45,405,810,24` for its `<p>` — Σ 864, 15% of the
  catalog — while the `<details>` was summary-height and the rect **overlapped
  the following sibling** (the cheap tell: no real in-flow box can do that).
  **Simple's zero-size box was correct**; the differ was wrong. Use
  `el.checkVisibility()` as the ground truth — it is false for `display:none`
  and content-visibility-hidden subtrees and stays **TRUE** for
  `visibility:hidden` and `opacity:0`, which occupy layout and must keep being
  compared. Round 22 emits `rendered=` per element in the walker and routes it
  into the round-20 boxless arm. **Never drop rows from the walk** — the
  nth-path key is an ordinal, so removing one shifts every later sibling.
- **Count the blast radius before writing a layout fix.** `position=absolute`
  occurs **once** in all 1583 catalog elements; one grep proved the shrink-to-fit
  change could not regress the catalog and moved the burden of proof onto the
  spec, where it belongs.
- **`right: auto` is NOT honoured** (890 vs Chrome's 77) — a separate
  offset-keyword parsing defect, filed
  `doc/08_tracking/bug/absolute_right_auto_not_honoured_2026-09-14.md`, 0 Σ on
  the catalog. Do not fold it into a width change: it would alter the
  both-offsets stretch arm's `st.right_px >= 0` test.
- **After round 22 the catalog's error is no longer concentrated.** `html` is
  **76% of remaining Σ (2533 of 3312)** with its top row at only Σ 224 (8.8%).
  Rank `html` by FEATURE CLUSTER, not by single row — the round-21 "find the one
  big row" method is now exhausted.

Round 20 measurements: `doc/10_metrics/ui/web_chrome_parity_round20_2026-09-14.md`.
Round 21 measurements: `doc/10_metrics/ui/web_chrome_parity_round21_2026-09-14.md`.
Round 22 measurements: `doc/10_metrics/ui/web_chrome_parity_round22_2026-09-14.md`.

## Round 23 (2026-09-14) — rank the ORIGINATING deltas, not the raw Σ

- **Raw root-row Σ over-weights cascade.** Clustering round 23's baseline put
  `html/block-flow/li` on top at Σ 1597 across 49 rows — almost all of it `dy`
  inherited from a height error in an EARLIER sibling. Re-rank on
  `|dx| + |dw| + |dh|` only (drop the pure-`dy` followers), then attribute each
  shift to the rows downstream of it: `shift x downstream_root_rows`. That moved
  the `<pre>` row (dh 24, 44 rows below it, ~1150 attributed) above the `<wbr>`
  row (dh 168 but only 2 rows below it, ~1000). Check the arithmetic against
  `<body>`'s own `dh` — the signed originating shifts must sum to it exactly.
- **Σ can fall 42% with the mismatch COUNT unmoved, and that is not a failure.**
  Shortening a cascade leaves every downstream row non-zero but small, and the
  differ's threshold is 1 px. The count falls only when a cascade is removed.
- **`white-space: pre` is not `nowrap`.** They had shared one `Style` flag;
  `pre` PRESERVES newlines, `nowrap` COLLAPSES them. The discriminator is
  `<div style="white-space:pre">A\nB</div>` — if it fails identically to
  `<pre>`, the newline reaches layout and layout throws it away, so it is NOT a
  missing UA rule. Two HTML rules must be harvested, not recalled: a newline
  immediately after `<pre>` is dropped, and a trailing newline opens no line.
- **`overflow-wrap: normal` forbids breaking inside a word.** A word wider than
  the line overflows. The worst case is a run that STARTS mid-line, where
  `max_width` is a pen remainder of a few pixels and the old `endv == start` arm
  emitted one codepoint per line (9 lines for "BreakHere"). Keep intra-word
  breaking reachable for `break-word`/`anywhere`/`break-all` — that control is
  what makes the rule statable.
- **`<wbr>` is boxless AND a break opportunity; only the first is implemented.**
  The control that proves the fix must be tag-scoped: `LongWord<i></i>BreakHere`
  is ONE line in both engines, so a run boundary alone is correctly not a break.
  Filed `doc/08_tracking/bug/wbr_not_a_soft_break_opportunity_2026-09-14.md`.
- **A fix that is right in two contexts and wrong in a third is a compensating
  error — back it out.** Seeding the line box from the container's strut (CSS
  2.1 10.8.1) fixes `<sub>` in the catalog and under no author CSS, and is
  contradicted under `font: 16px/1.5`, where Chrome measures 20 for a div whose
  strut would be 24. Round 23 reverted it rather than land the catalog green on
  an unstatable rule:
  `doc/08_tracking/bug/sub_sup_line_box_strut_contradiction_2026-09-14.md`.
- **From a detached worktree the freshness gate fails closed** on a missing
  `build/cargo-r2/release/simple`, and `simple test <dir>` additionally needs
  `bin/simple` to exist. Symlink both to the main tree's artifact and RECORD
  that the check path differs from prior rounds.

Round 23 measurements: `doc/10_metrics/ui/web_chrome_parity_round23_2026-09-14.md`.

## Round 24 — one defect, two top-ranked roots

- **Rank on ATTRIBUTED Σ and the ranking changes under you.** The standing
  "`<wbr>` ~1000" lead was stale the moment round 23 landed: that row is now
  +24 over 4 rows, ~96 attributed. Re-derive the ranking from run A every
  round; do not inherit last round's list.
- **Pin the sign convention from a row whose two absolute values you know.**
  `li` 86 is Chrome 48 / Simple 24 and prints `dh=+24`, so `dh = Chrome −
  Simple` and a positive `dh` means Simple is SHORT. Round 23's prose has this
  backwards in one sentence.
- **Two differently-shaped symptoms on two pages were ONE defect.** An `<hr>`
  demo box 8 px short on `html.html` and a 16 px page-wide shift on
  `animation.html` were both "a block's bottom margin is dropped in front of an
  anonymous inline run". Before opening two investigations, check whether the
  lost distance equals the preceding block's `margin-bottom`.
- **A root at the TOP of a page is worth far more than the same root two thirds
  down.** Fixing the animation head removed 62 mismatches; fixing `<hr>` removed
  zero, because its cascade rows only shrank from 6 to −2 and the differ's
  threshold is 1 px. Predict count and Σ separately.
- **Predict, then record the misses.** Round 24 predicted `forms-media`
  unchanged; it improved 189 → 117, because the same defect sat in its `<form>`
  and the ranking had only diagnosed the top two pages. Under-scoping a
  diagnosis to the pages you ranked is the recurring miss.

Round 24 measurements: `doc/10_metrics/ui/web_chrome_parity_round24_2026-09-14.md`.

## Round 25 — `<wbr>`, and the value of a prediction that MISSES

- **Pin the Σ DEFINITION before ranking, not after.** Σ in every round of this
  series is `|dx|+|dy|+|dw|+|dh|` summed over `inherited: false` rows ONLY.
  Summing all rows on this baseline gives 3223 against the reported 1258 — a
  2.6× discrepancy that would silently invalidate every before/after table.
  Resolve it against a small page's own `.geometry_diff.md` root table
  (`css-layout`: 9 + 8 + 1 = 18) before touching any code.
- **The biggest root is not always the one to take.** `<sub>`/`<sup>` is ~380
  attributed here, three times the next root, and is filed as a measured
  contradiction. Rank by attributed Σ, then take the largest ACTIONABLE row and
  say in writing which rows you skipped and why.
- **A prediction that misses is worth more than one that hits.**
  `Long<wbr>Word<wbr>BreakHere` in an 80 px box was predicted 72 and measured
  **48**: Chrome's line breaker is GREEDY, taking only the opportunity it needs,
  so the first `<wbr>` is passed over. The eager implementation would have
  matched the catalog's single `li` 86 perfectly and been wrong. Always harvest a
  MULTI-opportunity case, not only the one the catalog shows you.
- **Measure the first WORD, not the whole run.** A soft-break arm that tests the
  following run's full advance breaks at opportunities Chrome passes over. The
  helper is `first_word_advance_width` — everything up to the first collapsible
  space.
- **Two sabotage arms must fail DIFFERENT AC sets.** Disabling the arm fails
  AC-1/AC-2; inverting the fit test fails AC-2/AC-4/AC-5. Same failing set from
  both arms means one of them is not testing what you think.
- **A `<br>` `dx` row is not a `<br>` placement bug.** Simple already places
  `<br>` at `ix + inline_x`, which is Chrome's rule, so css-paint's `dx`
  49/24/8 says the PEN is short at those points — a text-advance
  under-measurement on the preceding runs. Discriminate the `<br>` rect from the
  following run's rect in the fixture before editing anything.
- **`strong`/`b` `dw` deficits look like ONE root: bold metrics.** `overview` is
  29 of 34 Σ this shape (a `strong` 6 px narrow, then four siblings each `dx`
  +6 behind it); `html` shows `strong` +9 and `b` +4. `<q>` +10 is a different
  root in the same rows — Chrome's UA quotation marks, which Simple never emits.

Round 25 measurements: `doc/10_metrics/ui/web_chrome_parity_round25_2026-09-14.md`.

## Linux aarch64 pixel round — 2026-11-14 (Chromium 131, Playwright)

Gate: `scripts/check/check-chrome-catalog-pixel-diff.shs`; ratchet rows in
`scripts/check/chrome_catalog_pixel_diff_baseline.Linux-aarch64.txt`.

| page | before | after |
|---|---|---|
| overview | 6.45 | 2.03 |
| html | 26.94 | 15.77 |
| css-layout | 17.19 | 5.89 |
| css-paint | 18.26 | 7.46 |
| forms-media | 18.76 | 8.64 |
| animation | 33.89 | 23.98 |
| evidence | 2.31 | 1.63 |
| tab-bar | 0.61 | 0.61 |

Oracle trap: playwright 1.49 pins Chromium 131, which still shrinks
`section h1`; Chrome 159 does not. A sectioning-h1 rule added from the 131
oracle was reverted the same day. Use the NEWEST Chromium the host has.

Roots fixed, each pinned by a spec: Linux generic faces (Liberation Sans /
DejaVu Sans Mono + real bold/italic faces — Linux used Noto Sans SC's wght=100
master and reused the regular face for bold), list
markers and link underlines never painted in Draw IR, staged glyph pen drifting
from the measured advances (last glyph clipped), bare `#text` runs missing
their half-leading.

Traps measured this round:
- **No Chrome on linux-arm64.** `npx playwright install chromium` is the no-root
  path; the gate finds `~/.cache/ms-playwright/chromium-*/chrome-linux/chrome`
  or takes `CHROME_BIN`. AppArmor-restricted userns hosts need
  `CHROME_NO_SANDBOX=1`.
- **`--headless=new --window-size=W,H` is a WINDOW size.** The viewport was
  900x673 for 900x760 (87 rows of browser UI) and the screenshot pads below it,
  so any page taller than 673 px compared Simple content against padding. The
  gate probes the deficit and captures a taller window; `pixel_diff.spl` crops
  only when told (`--ref-viewport-rows`). For hand oracles use
  `chromium_headless_shell-*/chrome-linux/headless_shell` (viewport == window).
- **A comparison is not a verdict.** The gate printed `PASS … worst=33.89`;
  PASS meant "a diff ran". Without a baseline file the verdict now says
  `compared, not judged`.
- **One seed binary lies.** `src/compiler_rust/target/bootstrap/simple` (built
  2026-11-05, bootstrap profile) returns `"760".to_i32() == 95` under its JIT; a
  release seed built from current source is right. The two differ in age,
  profile and features, so the cause is not isolated — record the binary with
  any number and re-run on another before chasing an inexplicable value.
- **Never edit the worktree while a render reads it.** `src/lib` is read as
  source on every run; pages rendered across a cherry-pick are mixed-source.
- CPU vs Vulkan on `overview`: 69 differing px, all at clipped run ends — a
  cheap cross-backend probe that located the clip in the CPU lane.

Open, in size order: `animation` (wrapped inline text continues under its own
run start instead of the line box's left edge; canvas/svg/audio/video row not
painted and over-tall), `html`, `forms-media`, `css-paint`, `css-layout`.

## 2026-11-14 — mid-line text runs wrap into the line box, not their own column

- **Model.** A `#text` that starts mid-line (after an inline sibling) and wraps
  owns the WHOLE line box (`bx` = line left, `bw` = line width); only line 0 is
  inset, by `LayoutResult.first_line_dx[node]` (empty when no run needs it).
  Both painters add the inset to line 0 exactly where `text_indent_px` is
  added; read it through `text_first_line_dx_at`. Any new `LayoutResult(` /
  `TextWrapCache(` that feeds a painter MUST copy the field, or the old
  hanging-indent paint silently returns on that path.
- **Three arms** in the inline run loop (`..._layout_engine.spl`): first word
  fits the remainder -> inset run; it does not -> break the line BEFORE the
  run (as `<wbr>` does); inline content after a wrapped run continues on the
  run's LAST line behind its tail.
- **Not modelled:** an inline ELEMENT that starts mid-line and wraps
  (`text <span>long …</span>`), centred/right/RTL runs, float-band lines.
- **Trap — Chrome's text-node rect includes the collapsed leading space.**
  `Range.getClientRects()` line 0 x is the pen BEFORE the space; the first
  glyph (what the renderer's box reports) is one space advance further right.
- **Trap — `.len()` on `text` is codepoints in current seeds, bytes in the
  Nov-5 seed.** The wrap path indexes bytes; a `by.len() != txt.len()` arity
  check silently drops every non-ASCII run to the flat estimate. Use
  `byte_len()` for byte arity. Still open elsewhere in the style/metrics stage:
  a lone `<p>— partial; values</p>` measures 160 px on the current seed vs 119.
- Spec: `test/01_unit/browser_engine/inline_text_wrap_line_box_spec.spl`.
## 2026-11-14 — combination matrix vs Chrome 159 (tag x tag, tag x CSS, CSS x CSS)

`sh scripts/check/check-web-combo-matrix-chrome.shs` (about 45 s; set
`SIMPLE_BIN`): 979 generated cells / 3880 element ids (849 / 3415 before the `lh_normal` page) in
`test/fixtures/browser/combo_matrix/` (generator:
`scripts/generate/generate-web-combo-matrix.shs`), each cell in its own 400x140
slot and compared slot-relative at 1 px. It is a RATCHET on
`scripts/check/web_combo_matrix_baseline.txt`: a fix must delete the rows it
turns green in the same change, or the check FAILs as stale.

- Matching after the first three fixes: 544 / 849 cells (64.1%).
- Open clusters, largest first (cells): form-control UA size, i.e. `button`
  and `input` have no UA border and `input` a different content width (78);
  table-cell residue: max-content width drops the spaces around an inline child (9), a `td` whose `display` is not `table-cell` is not laid out (8);
  `sub`/`sup` (36, CLOSED -- see the sub/sup section below); floats (34, CLOSED -- see the float section below); `fieldset`/`legend` (24); `flex-grow` on an (row/wrap CLOSED, see below)
  item with a definite width (17); monospace metrics for `code` (16); width /
  height / vertical padding applied to non-replaced inline boxes (15).
- **`parse_int` drops the sign.** Any signed CSS integer read through it is
  wrong for negatives; `left`/`top`/`order` were fixed, `right`/`bottom` are
  not, because `right_px >= 0` doubles as "right is set".
- **`left:10%` is read as 10 px**: offsets have no percentage form yet.
- The Chrome harvest is `check-chrome-layout-geometry-diff.shs --harvest
  <page> <out>`; rows now end in `id=<id>`. Use the headless shell under
  `~/.cache/ms-playwright/chromium_headless_shell-*` (viewport == window); the
  131 build has an outdated UA stylesheet.
- Record: `doc/08_tracking/bug/web_combo_matrix_signed_offset_order_flex_basis_2026-11-14.md`.
- Table UA defaults (`border-spacing:2px`, `td,th{padding:1px}`) landed with
  the matrix; spacing is forced to 0 under `border-collapse:collapse` in the
  layout, because the default is no longer 0. Record:
  `doc/08_tracking/bug/web_table_ua_border_spacing_and_cell_padding_2026-11-14.md`.

## State at landing (2026-11-14, Chrome 159.0.8154.6, Linux aarch64)

- Catalog pixel gate, 900x760 `cpu_simd`: overview 2.88, html 15.98,
  css-layout 6.11, css-paint 9.28, forms-media 6.38, animation 12.23,
  evidence 1.72, tab-bar 0.68 (baseline row 0.63, inside the +0.25 tolerance).
- Combination matrix: 608 of 849 cells match (71.6%); 463 element ids baselined.
- **The matrix verdict depends on WHICH Chrome 159 binary runs it.** Full
  Chrome (`chromium-1255/.../chrome`, `--headless=new`) gives 241 mismatching
  cells; the headless shell gives 259 (21 `<code>` cells: generic `monospace`
  is 192.66 px in full Chrome, 192.03 in the shell). The baseline is measured
  with full Chrome; set `CHROME_BIN` to it.
- **Two paint lanes, one layout.** The software-pixel lane paints text below
  16 px with the 5x7 bitmap rasteriser; Draw IR lanes paint the resolved face.
  `web_set_bitmap_paint_lane` keeps the bitmap advance clamp on for the
  software entry points only. Dropping the clamp everywhere joins `ll` at 13 px.
- 4K (3840x2160, Vulkan on llvmpipe) is ratcheted in
  `chrome_catalog_pixel_diff_baseline.Linux-aarch64.3840x2160.vulkan.txt`:
  overview 0.24 (9.15 before the clamped-width auto-margin fix), html 2.77,
  css-layout 2.09, css-paint 2.50, forms-media 1.96, animation 2.63,
  evidence 0.15, tab-bar 0.05. About 2 min per page on llvmpipe. Not yet
  measured on a hardware Vulkan driver.
- Open review items: `doc/08_tracking/bug/web_render_chrome_lane_review_residue_2026-11-14.md`.

## 2026-11-14 — replaced media (canvas / svg / audio / video) vs Chrome 159

- **Oracle trap:** Chromium 131 scales a media-less `<video>` 2:1 from one
  specified axis (`width=120` -> 120x60). Chrome 159 does not (120x150). Any
  number taken with the chromium-1148 build must be re-measured.
- The 300x150 default is a CONTENT size: an auto axis of canvas/svg/video adds
  the element's own padding and border even under `box-sizing:border-box`
  (310x160 with `border:2px;padding:3px`). `<audio controls>` is an explicit
  UA size and stays 300x54. `<audio>` without `controls` is `display:none`.
  Owners: `replaced_auto_box_w` / `replaced_auto_box_h`
  (`simple_web_html_layout_renderer_layout_foundation.spl`), shared by the
  final box and the inline pen prediction.
- Paint is lowered to Draw IR rects in `_html_draw_ir_replaced_media_commands`
  (`simple_web_html_layout_renderer_paint_layout.spl`): svg `<rect>`, the
  `<video controls>` panel (#333 -> #000), the `<audio controls>` pill
  (#f1f3f4). A video WITHOUT `controls` is transparent in Chrome — the dark
  box is the controls panel, not a video surface.
- The skia SVG rasteriser (`std.skia.feature.codec.svg_render`) is not wired:
  the Draw IR result cannot return an image resource.
- Measured: catalog `animation` 12.23% -> 7.36%; `forms-media` 6.38% unchanged;
  combo matrix unchanged (463 baselined ids, 0 new, 0 stale).
- Residues: `doc/08_tracking/bug/web_replaced_media_residues_vs_chrome_159_2026-11-14.md`.

## 2026-11-14 — svg viewBox / percentage / em sizing, self-closing foreign elements

- A valid `viewBox` gives an `<svg>` a ratio and NO size: one specified axis
  derives the other on the content box; with both auto the width is the
  available width (`viewBox="0 0 200 50"` in 900 px -> 900x225). Owners:
  `replaced_auto_box_w/h`, `svg_view_box_milli` (shared with the painter).
- **Inline percentage trap:** `layout_with_style` receives the predicted pen
  width for an inline child, so a percentage width must be resolved at the
  inline-run site (`inline_media` in `layout_engine.spl`), not inside it.
  A percentage height against an auto-height container computes to auto.
- `width`/`height` in `em` went through `parse_int` (`height:1em` = 1 px);
  they now use `_decl_font_relative_length_px` in BOTH declaration paths
  (`decl_apply.spl` and the dispatch fast path in `declarations.spl`).
- `html_tree_builder` honours the tokenizer's `self_closing` flag only in
  svg/math foreign content (`_TreeStack.in_foreign_content`); `<div/>` stays
  open, as in Chrome.
- **Ratio-only svg and shrink-to-fit:** it contributes 0 to min/max-content
  (a specified height contributes `height x ratio`) and then fills the width
  the container resolved to. `intrinsic_text_width` serves BOTH shrink-to-fit
  and a span's pen prediction, so a span holding such an svg takes the line's
  available width instead (`inline_box_holds_ratio_only_svg`). A floated or
  absolute replaced box is not shrink-to-fit: size it with
  `replaced_auto_box_w` against the available width.
- **1 px box floor:** an empty inline-block is 1x1 here, 0x0 in Chrome; 0-wide
  oracle rows are asserted as `<= Chrome + 1`. `display:inline-flex` is
  dropped by the cascade as unsupported (the box stays a full-width block);
  `Style.display_inline_flex_authored` records it so an unsized svg there
  keeps the 300x150 default instead of filling the row. A flag set in
  `apply_authored_style_metadata` only sees INLINE styles: stylesheet rules
  are applied without display, so set display-derived flags beside
  `_final_authored_display` in `core.spl`.
- **Self-closing flag:** a `/` before `>` is the flag only when it is not
  the tail of an UNQUOTED attribute value (`<a href=/x/>` has `href="/x/"`);
  `_trailing_slash_self_closes` in `html_tokenizer.spl`. HTML integration
  points (`foreignObject`, `desc`, `mi/mo/mn/ms/mtext`, `annotation-xml` with
  an HTML encoding) end foreign content in `_TreeStack.in_foreign_content`.
- **Span holding a ratio-only svg:** `inline_box_ratio_only_svg_fill_w` adds
  the svg's constrained fill width to the span's intrinsic width; it skips
  out-of-flow svgs and is scanned once per inline subtree. Derived viewBox
  sizes saturate at 33554432 px (`svg_ratio_scaled_px`).
- **Out-of-flow child of a span:** `iw` inside a span is the span's own
  width, so a float / absolute REPLACED child is sized through
  `inline_parent_containing_block` (nearest block container; for an absolute
  box the nearest positioned ancestor, tested on EVERY ancestor including
  inline ones, with insets and percentages resolved against it), and `intrinsic_text_width` skips out-of-flow children
  of an inline box. `svg_ratio_view_box_milli` is the viewBox for SIZING (it
  drops Chrome's unusable sub-unit-wide ratios); the painter keeps
  `svg_view_box_milli`.
- `style_rule_index.spl` scans raw markup on its own; its self-closing test
  is the tokenizer's `html_start_tag_content_self_closes`, not `ends_with("/")`.
- Open from follow-up 2: residues 12-14 (non-replaced absolute box in a span;
  svg `title` dropped; the exact-10^7 ratio boundary).
- Still open: residues 6-11 (9: a rule `em` is resolved before an inline
  `font-size`; 11: the 1 px floor, inline-flex, percentage width in a
  shrink-to-fit container) in
  `doc/08_tracking/bug/web_replaced_media_residues_vs_chrome_159_2026-11-14.md`.
## 2026-11-14 — `font-family` is a LIST, resolved name by name

`font_provider.spl` used to classify the whole `font-family` value by substring
(`mono`, `code`, `sans`, `arial`, ...) with the mono stack as the unmatched
default. One resolver, `browser_resolve_font_family`, now walks the list in
order (CSS Fonts 4 §5) and feeds every consumer: the candidate list,
bold/italic routing, the bundled lookup, the host-face test, the
`font_renderer.spl` category and the layout `style_font_is_monospace` test.

Chrome 159.0.8154.6 (Linux), width of `Hamburgefonstiv 0123` at 16px in an
inline-block span — the width identifies the face:

| font-family | Chrome | Simple before | after |
|---|---|---|---|
| `"IBM Plex Sans", Arial, sans-serif`, `Arial`, `Helvetica`, `sans-serif` | 160.98 (Liberation Sans) | 161 | 161 |
| `serif`, `"Times New Roman"`, `Times` | 147.69 (Liberation Serif) | 148 | 148 |
| `NoSuchFont`, `Roboto`, `"Segoe UI"`, `Verdana`, `cursive`, `fantasy`, `ui-monospace` | 147.69 | 193 | 148 |
| `ui-sans-serif`, `-apple-system` | 147.69 | 161 | 148 |
| `"Source Code Pro", Arial` | 160.98 | 193 | 161 |
| `system-ui`, `"DejaVu Sans"` | 183.91 (DejaVu Sans) | 161 | 184 |
| `"Courier New"`, `Courier` | 192.03 (Liberation Mono) | 193 | 192 |
| `monospace` | 192.66 (DejaVu Sans Mono) | 193 | 193 |

Traps:

- **Which Chrome.** Generic `monospace` is 192.66 in full Chrome and 192.03 in
  `chrome-headless-shell` of the same version (no fixed-font preference, so
  Blink's "Courier New" default). The combo-matrix baseline is full Chrome:
  the headless shell reports 259 mismatching cells where full Chrome reports
  241, all of the difference in `<code>` cells.
- **The blocky text in `web_render_page_ppm.spl` output is not a family bug.**
  The `cpu_simd` lane paints every family with the 5x7 bitmap face at
  `font_size / 8` scale (`fb_text_thin_scaled_clip_range`). Measure widths with
  `simple_web_layout_debug_layout_by_id`, or render through
  `simple_web_render_html_to_pixels`, before blaming resolution.
- **Scope gate.** The per-name walk runs only where the measured face set
  exists (`browser_host_has_measured_linux_face_set`: Liberation Sans, Serif
  and Mono, no macOS system faces). **macOS is unmeasured** and keeps the old
  substring classification verbatim (`_browser_resolve_family_legacy`), as does
  any host without Liberation.
- **Non-CSS literals.** `""`, `inherit` (common/ui/style.spl) and bare `sans`
  (panel2d, widget_draw_ir, window_scene_draw_ir) are not CSS lists and keep
  the stack they had. Chrome resolves bare `Sans` to DejaVu Sans; Simple does
  not follow it for that reason.
- **`line-height: normal` is the face's own metric, for text AND elements.**
  A #text style used the resolved metric (`font_size` on the pure-Simple
  outline lane) and an element style used `9 * (font_size / 8)`; `style_line_h`
  now asks one source, `browser_normal_line_height_px` (font_renderer.spl):
  ascent, descent and line gap, each scaled and rounded ON ITS OWN, then
  summed (rounding the sum gives Liberation Serif 14 at 12px; Chrome says 15).
  Chrome 159 at 12/16/24/32px: Liberation Sans 14/18/28/37, Liberation Serif
  15/18/27/37, DejaVu Sans Mono 14/19/28/38. Source is the `OS/2` typo metrics
  when USE_TYPO_METRICS is set (Chrome honours it: Pagul 17/34/68), else `hhea`.
  Measured-Linux-host only; `ResolvedFontMetrics.line_height` (non-web text) is
  untouched everywhere.
- **Gates that do not move are not evidence.** The combo matrix and the 8-page
  catalog all declare `font: 16px/1.5`, so neither exercises `line-height:
  normal`; prove a line-height change with a page that uses it
  (`wrapped_line_advance_normal_line_height_spec.spl`).
- **A test page with no `font-family` is SERIF in Chrome and sans in Simple**
  (Style default). Set the family in every oracle page or the numbers compare
  two faces.
- `line-height: 150%` was 150x and `line-height: normal` could not override an
  inherited factor; both fixed with the above. Residuals are listed in
  `doc/08_tracking/bug/web_wrapped_line_advance_16px_vs_chrome_18px_2026-11-14.md`.
- The legacy (unmeasured-host) classification is pinned on every host by
  `font_family_legacy_classification_spec.spl`, which calls
  `_browser_resolve_family_legacy` directly.

Specs: `test/01_unit/browser_engine/font_family_list_resolution_spec.spl`,
`font_family_generic_classification_spec.spl`.
## Looking at a comparison yourself (2026-11-14)

`SIMPLE_COMPARE_VIEW=stay|auto` (default off) makes Chrome-vs-Simple and
Skia-vs-Simple-2D comparison sites write both buffers to
`build/compare_view/<name>/` and open a viewer sized to the host screen
(side by side -> tabs -> fit/scrollbars). New comparison code should call
`compare_view_inspect` from `std.nogc_sync_mut.ui.compare_view_host`.
Design and migrated sites: `doc/05_design/ui/web_diff/compare_view_inspection.md`.

## 2026-11-14 — selector combinators, `:has()` with context, and the step budget
The layout matcher (`simple_web_html_layout_renderer_core_selectors.spl`) has
ONE An+B evaluator (`css_nth.spl`), `+` / `~` combinators, `:nth-*` (incl.
`An+B of S`), contextual `:has()` and a backtracking right-to-left walk, on
both the text and pre-parsed paths; every row is pinned against Chrome 159 in
`test/01_unit/browser_engine/{structural_pseudo_class,nth_child_of_selector,selector_hardening}_chrome_parity_spec.spl`.
Trap: CSS is untrusted, so one match is capped at 100,000 compound steps and
exhaustion must fail CLOSED everywhere (never negate an exhausted `:has()`,
never cache an answer computed while exhausted) —
`selector_sibling_complexity_spec.spl`. Known residual limits:
`doc/08_tracking/bug/web_selector_budget_residual_limits_2026-11-14.md`.



## 2026-11-14 — floats and `clear` (matrix 241 -> 205 mismatching cells)

- **Model.** `simple_web_html_layout_renderer_layout_engine.spl` keeps a float
  context: every placed float's MARGIN box in page coordinates
  (`g_float_side/x0/x1/y0/y1`), queried by `float_ctx_left_edge` /
  `float_ctx_right_edge` / `float_ctx_next_bottom` / `float_ctx_clear_bottom`.
  `layout_with_style` is now a thin wrapper over `layout_with_style_flow`: a
  box that establishes a block formatting context (`float_ctx_establishes_bfc`)
  gets its own slice of the list (`g_float_base`) and drops it on exit, and its
  auto height grows to enclose its floats.
- **Placement** (`float_ctx_place_y`): not above the previous float's top,
  below the floats `clear` names, then down past float bottoms until the
  margin box fits. A cleared FLOAT keeps its top margin below the clearance; a
  cleared BLOCK's border top sits at the clearance and its margin is absorbed.
- **Line boxes.** The inline run loop refreshes `inline_start_x` / `line_iw`
  from the float context at every line start (`inline_base_x` is the float-free
  start). A float met inside an open run joins the line if it fits and moves
  the boxes already on it (`line_nodes`) right.
- **Trap — the old band narrowed by the RUN's width.** `node_w` in the `#text`
  branch is the run's own box, so `node_w - indent` went to 1 px and `bb` beside
  any left float wrapped to two lines (every `…-b` cell was 48 px tall). The
  narrowed width comes from the run loop (now as per-line boxes, see the
  "per-line text boxes" entry below).
- **Trap — a `%` width float was resolved twice** (50% of 400 gave 100): pass
  `style_with_width(cst, resolved)` like the inline-block arm does.
- **Trap — page coordinates go stale when a subtree is translated.** The
  margin-collapse re-top calls `float_ctx_shift`; any NEW
  `offset_layout_subtree` on a non-BFC block that can hold floats must too.
- **Not modelled:** a FLOAT is fitted at its top row only, not over its whole
  height; a run that starts mid-line beside a float; `td` floats; the
  collapsed space after an inline float is counted twice (`aa <float> bb`,
  about 5 px). The full list is in the residue bug record.
- **Found, not float-related:** a 100 px block wraps
  `one two three four …` into 9 lines against Chrome's 7 (`one two three` is
  96.95 px but does not fit 100); `<span>bb</span> cc <b>dd</b>` puts `dd` 6 px
  right of Chrome.
- Spec: `test/01_unit/browser_engine/float_clear_chrome159_geometry_spec.spl`.

## 2026-11-14 — `<sub>` / `<sup>` join the line box (matrix 205 -> 167 cells)

- **Cause.** A `vertical-align: sub | super` box was laid out at line top
  +- font-size/4 and never entered `inline_baseline_nodes`, so the line box
  could not grow (every block 3 px short, 5-6 px in a heading). `<sub>`/`<sup>`
  also reset `line-height` to normal; html.css sets only `vertical-align` and
  `font-size: smaller`.
- **Model (Blink).** Baseline lowered by parent-font/5 + 1 (sub) or raised by
  parent-font/3 + 1 (super): `vertical_align_baseline_shift`. In
  `align_inline_line_baselines` a plain inline element's ascent/descent are
  `inline_box_shifted_ascent/descent` -+ its own shift, which also walks the
  sub/super boxes NESTED in it (`<b>x<sup>2</sup></b>` grows the line and
  lowers `<b>`). The shifted box's top is `baseline + shift -
  inline_content_area_ascent`.
- **Two placements.** On a block's line the aligner places the box. Inside an
  inline parent (`st.display == "inline"`) the run loop places it from the
  parent's content-area top, because that parent's box must stay its content
  area. Inline-block / replaced boxes with sub/super keep the flat nudge.
- **Trap — integer metrics drift 1 px per term.** Deriving the top from
  `strut offset` and `half-leading` separately lost 2 px; go through
  `inline_content_area_ascent` once.
- **Found, not fixed:** `line-height: normal` on a block does not override an
  inherited unitless factor (block stays 24 px, Chrome 18-21); the
  `td`/sub cells are the table-cell max-content residue, not sub/sup.
- Spec: `test/01_unit/browser_engine/sub_sup_baseline_shift_chrome159_spec.spl`.

## 2026-11-14 — `flex-grow` on an item with a definite width or basis (matrix 167 -> 152 cells)

- **Cause.** The nowrap row pass split items into "explicit" (width or basis:
  never grows) and "auto" (shares the remainder by weight). `flex-grow` on an
  explicit item was ignored and the free space went to `justify-content`; a
  basis + grow item with no auto sibling took the WHOLE remainder and pushed
  its siblings out. The wrapping pass did compute a grown width but laid the
  item out with its authored `width`, which won.
- **Fix.** `grow_definite_total` collects flex-grow of definite-base items
  (`flex_item_definite_base_w`); positive free space is split
  `definite : auto` by grow weight (`definite_grow_space`), each definite item
  gets `base + share` (cumulative rounding) and is laid out through
  `style_with_width` so percentages inside it resolve against the used width.
  `justify-content` gets no space when anything grows.
- **Not fixed:** `flex-direction: column` ignores flex-grow (`.i flex-grow:1`
  in a 90 px column stays 24, Chrome 42) and `column-reverse` is laid out as a
  row; a wrapped line's items are not stretched to the line height
  (`align-content: stretch`, 24 vs 45); a growing item with AUTO width still
  starts from base 0 instead of its content width (`flex-grow:1` on two text
  items gives 141/141, Chrome 111.73/170.47), because `flex-basis: 0` and
  `auto` share the `flex_basis_px == 0` encoding.
- Spec: `test/01_unit/browser_engine/flex_grow_definite_size_chrome159_spec.spl`.

## 2026-11-14 — follow-ups to the float / sub-sup / flex-grow fixes

- **Trap — `layout_selected` bypasses `layout()`.** The `contain: layout`
  boundary is re-laid-out through `layout_with_style` directly, so any state
  `layout()` resets must be scoped another way. Floats: a `contain: layout`
  box is a formatting-context root in `float_ctx_establishes_bfc`; without
  that, a second partial pass placed each float beside its own stale copy
  (AC-14 of the float spec: 3 boxes differed from the full pass).
- **Not modelled, sub/sup:** when `<sup>` follows a WRAPPED text run, the
  reopened last line lowers its baseline for the sup but the run's own last
  line (part of the tall text box) does not move, so words before and after a
  footnote marker can differ by 2-3 px in paint. Element geometry matches
  (`sup` at y=26 in a 200 px `<p>`, Chrome 26).
- **Not modelled, flex:** `flex: 1` on an item that also has a `width` now
  grows from that width; Chrome grows from basis 0. Equal widths give the
  same result, unequal ones do not (`flex-basis: 0` and `auto` share one
  encoding).
- **Bitmap lane.** `check-simple-web-engine2d-js-bitmap-evidence.shs` refuses
  the Rust seed (`simple_bin_status=forbidden`) and needs a self-hosted
  `bin/simple`; on a host without one it reports `unavailable`, not a verdict.

## 2026-11-14 — paint follows the float inset; an explicit zero flex-basis overrides width

- **Per-line text boxes.** `LayoutResult.first_line_dx` is the mid-line inset
  of line 0 and nothing else (never negative). A run whose lines floats
  shorten has `LayoutResult.line_boxes[node]`: flat `(dx, width)` pairs, one
  per line; lines past the list span the box. A node has one form or the
  other. Read BOTH only through `text_line_box_dx` / `text_line_box_w`
  (`..._layout_foundation.spl`); the readers are both raster loops, the Draw
  IR first-line command and its `_line{n}` loop, the `text_line_x0` probe,
  and the CPU layout execution port (`browser_cpu_line_box`, with
  `browser_cpu_line_insets_from_boxes` recovering both forms). Any new
  `LayoutResult(` / `TextWrapCache(` that feeds a painter must copy
  `line_boxes` as well as `first_line_dx`. Specs:
  `test/01_unit/browser_engine/float_band_text_paint_inset_spec.spl`,
  `float_line_fit_chrome159_spec.spl`,
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/cpu_execution_port_line_boxes_spec.spl`.
- **Trap — do not pack a second meaning into an existing integer table.** A
  first version encoded the float inset as a negative `first_line_dx` entry;
  a reader outside the renderer files (the CPU execution port) read the table
  raw and would have put line 0 about 65,000 px left. Grep `src/` for every
  reader before changing what a shared field means.
- **`Style.flex_basis_zero`.** `flex: <n>` / `flex: <n> <m>` / `flex-basis: 0`
  / `0%` set it; `flex_basis_px` stays 0. EVERY such item, with or without a
  `width`, has base size padding + border (`flex_item_zero_basis`), joins the
  definite-grow share and is laid out via `style_with_width`.
- **Automatic minimum size.** A zero-basis item never ends below
  `flex_zero_basis_floor_w`: its min-content width (`flex_item_min_content_w`,
  longest word from the RESOLVED advances), capped by a specified `width`;
  no floor when `min-width` is declared (`Style.min_width_set`, true even for
  `min-width: 0`) or the item clips. Nowrap rows freeze too-small shares at
  the floor and redistribute (`zero_fixed_w`); with no free space every one
  sits at its floor and takes no part in shrinking.
- **Trap — `_table_text_min_content_width` is a flat cell estimate** (11 px
  per character at 16 px): `Label` measured 55 against Chrome's 39.16. Use
  the resolved per-byte advances for anything compared with Chrome.
- **Trap — the old shorthand parser read numbers positionally**
  (`parse_nth_int`): `flex: auto` set nothing, `flex: 1 200px` made shrink 200.
  It is token-based now: unitless = grow, shrink; length or `auto` = basis.
- This supersedes the "`flex: 1` on an item that also has a `width`" item in
  the follow-ups section above.
- Open residue (one record):
  `doc/08_tracking/bug/web_combo_matrix_float_subsup_flex_residue_2026-11-14.md`.
- Catalog pixel ratchet, 900x760 `cpu_simd`, measured at the tip of this
  change: overview 2.88, html 15.98, css-layout 5.85 (row 6.11), css-paint
  7.44 (row 9.28), forms-media 6.38, animation 7.09 (row 7.36), evidence 1.72,
  tab-bar 0.68 (row 0.63, inside the tolerance, not raised). The three lower
  rows were lowered. The same three values were measured before the paint and
  zero-basis commits, so those two moved no catalog pixel.
- `check-text-len-unit-mix.shs` at this tip: 0 new rows; it still FAILs on two
  STALE baseline rows outside the renderer (`src/app/spipe/model/canonical.spl
  _json_escape`, `src/compiler/80.driver/driver_compile_vhdl_source_map.spl
  _json_escape`), present on the release tip as well.
- Base comparison (release tip `c1099bb7897` vs this change, same seed
  `sha256 08aba9746a813ee7…`, 59,635,056 bytes, 2026-11-14 09:32, `--simple-only`
  over overview + evidence + css-layout): mismatch identical on all three
  (2.88 / 1.72 / 5.85), so the float, sub/sup and flex changes move NO catalog
  pixel and the lowered rows record improvements that were already on the
  release tip. Render time 54.1 / 32.1 / 260.4 s base vs 54.5 / 32.7 / 259.2 s;
  max RSS 814 MB vs 820 MB. The text-len check FAILs identically on the base
  (0 new, the same 2 stale rows).
- A float's auto width takes the wider of `flex_item_max_content_width` and
  `intrinsic_text_width`: only the second sizes a replaced child
  (`svg_viewbox_percent_sizing_spec` AC-13 went 1 px wide without it).

## 2026-11-14 — review round: lines and blocks fit beside floats over their own extent

- **Line start.** The run loop probes the floats over `[cy, cy +
  line_probe_h)` (the block's line height), not one pixel row. An EMPTY line
  that cannot take its first piece (`inline_first_fit_w`: first word, whole
  nowrap run, or atomic box) moves to `float_ctx_next_bottom_span` and tries
  again -- two half-width float columns followed by `<p>` no longer stack one
  word per line. `<br>` with `clear` moves `cy` below the named floats.
- **Wrapped run.** `float_ctx_line_boxes(y, line_h, left, right)` gives one
  `(dx, width)` pair per line for as long as a float reaches below the line
  top; `compute_style_wrap_ranges_float_band` wraps into them and leaves a
  shortened line EMPTY when the next word does not fit it. The Draw IR text
  command's y is the line top + 3 at 16px/1.5 (half-leading), the same number
  Chrome's `Range.getClientRects()` reports.
- **Formatting-context block.** Placed where the room over `[top, top +
  height)` holds it; auto height comes from a trial `layout_with_style`
  whose result is discarded (safe because the box scopes its own floats and
  the text tables are re-recorded by the real pass).
- **Alignment.** `block_sole_inflow_child` replaces `child_count == 1` for
  the centred/right sole-text widening: a float sibling is not in flow. An
  RTL box with no declared `text-align` gets `start`.
- **Cost.** `g_float_max_y1` (lowest float bottom of the current context
  slice, saved and restored by the `layout_with_style` wrapper) lets every
  float query return at once for a row at or below it.
- **Baseline arithmetic.** The ratchet lists element IDS, the gate table
  counts CELLS; a cell has a slot id plus 1-3 element ids and is green only
  when all of them match. 463 -> 263 ids (200 removed) is 241 -> 152 cells
  (89 fixed). The gate FAILs on a mismatching id that is not baselined and on
  a baselined id that matches, so its PASS line is the proof that no
  still-mismatching id was dropped.
- Residue: `doc/08_tracking/bug/web_combo_matrix_float_subsup_flex_residue_2026-11-14.md`.

## 2026-11-14 — second review round: fallbacks, long words, wrap freeze, trial reuse

- **Trap — a "whole run" fallback is a floor of the whole paragraph.**
  `text_longest_word_advance` returned the run's advance when the style had
  no per-byte table (`compute_styles(..., vector_fonts: false)`), so every
  `flex:1` paragraph froze at its full width. A minimum must fall back to a
  WORD in the unit that lane wraps with (`style_char_w` cells), never to the
  run. Spec row AC-30 lays out with `vector_fonts: false`; keep a no-face row
  for any measurement that feeds a floor.
- **Trap — a specialised wrap must keep the general wrap's arms.**
  `compute_style_wrap_ranges_float_band` lacked the `word_end_byte` arm
  (long word overflows whole) and was entered whenever a float existed below
  the line, shortened or not (`line_boxes_shorten` is the precondition now).
- **Wrapping flex lines** freeze per line after measuring
  (`wrap_frozen` / `wrap_line_of`): a frozen item leaves
  `line_grow_totals` and `line_zero_excess`, the rest share the line.
- **Trial reuse.** The formatting-context fit stashes its trial layout into
  `out_*` and the scalars (`trial_height`, margins); the real layout is
  skipped when `(x, y, w)` are unchanged. Without it nested
  `overflow:hidden` + float cost 2^depth (22 levels did not finish).
- **`Style.text_align_set`** (inherited with `text_align`) separates an
  authored `left` from the initial value for the RTL `start` default.
- **Rounding.** Definite grow shares round to the NEAREST pixel
  cumulatively, which reproduces Chrome's rounded item edges (400 / 3 ->
  0, 133, 267).
- Still open (residue record): the exact float bottom for a word moved
  down inside a run, integer flex factors, the eager `float_ctx_line_boxes`
  list, `align="left"` under RTL, cell-estimate minimum without a face.
- Filed after the third review (residue items 25-27, and 6): the faceless
  float-aware wrap still chops long words (as the normal faceless wrap
  does); one twice-layout case remains when the room over a
  formatting-context box's height is narrower than at its top row;
  `<td align="left" style="direction:rtl">` probably still aligns `start`;
  the faceless cell wrap gives 6 lines where Chrome has 3 for the AC-30
  paragraph.

## 2026-11-14 — combined tip check (floats + line-height normal + selector combinators) and the `lh_normal` matrix page

- **No interaction regression.** At `2d9344c6eae` (three separately gated
  lanes merged) the matrix is 152 / 849 cells with 263 ids, 0 new and 0
  stale; the 8 catalog pages measure exactly their rows (tab-bar 0.68 against
  0.63, inside the tolerance). Nothing to tighten in either baseline.
- **Spec sweep.** 118 specs in `test/01_unit/browser_engine` plus the CPU
  port spec: 107 green. The 11 red ones fail the SAME cases at the pre-lane
  base `00afc10545b` (browser_renderer_utils closure 21/22, dom_identity_index
  5/6, fractional_advance_accumulation 4/11, html5lib_tokenizer 7/11,
  html_tree_builder_hardening 11/13, html_tree_builder 8/37, js_integration
  0/12, kern_pair_advance_accumulation 1/9, platform_system_face_metrics
  15/25, declarations closure 52/54, table_fractional_column_width 0/2).
  `corpus_fifth_line_exact_pixel_spec` (0/1) is `@tag:in-development` and
  documents its own expected failure.
- **`lh_normal.html`** (generator `page_begin` takes the body font as a third
  argument): 130 cells / 465 ids under `font: 16px sans-serif`, i.e. the
  initial `line-height: normal`, which no fixture covered -- every other page
  sets `16px/1.5`. Groups: tag-tag (7 parents x 10 children), font,
  font-inline, line-height, line-height-inherit, line-height-reset, wrap,
  box. Matrix is now 979 cells / 3880 ids.
- **Found and fixed through it:** a percentage or `em` `line-height` was
  stored as a factor, so a 24 px child of `line-height:150%` got 36 px
  (Chrome 24). It computes to a LENGTH against the declaring element's own
  font-size and is inherited as that length; only a unitless number stays a
  factor. Spec:
  `test/01_unit/browser_engine/line_height_percent_em_inherits_length_spec.spl`.
- **Trap — the length needs the element's FINAL font-size.** Declarations
  are applied once per matching rule, so `.a{line-height:1.5em}` plus an
  inline `font-size:32px` saw the stale 16 px when the length was computed
  at parse time (24 where Chrome has 48). The factor is kept on the Style as
  `line_height_em_milli` (thousandths, so `112.5%` survives), converted to
  `line_height_px` at the end of EVERY declaration application, reset by
  `inherit_from` / never passed by `inherit_style`, so children get only the
  length. Any other value that depends on a property which can cascade in
  later needs the same pending form.
- **Baselined clusters on the new page (17 cells, 27 ids):** `td` parents
  (10 cells: the known table-cell max-content residue, the cell wraps to two
  lines); inline button / small in `h1` / `h3` (3: baseline alignment of a
  smaller or atomic inline in a heading, same as the 1.5 page); `pre` with
  button / input (2: monospace form-control width, same as the 1.5 page);
  `<span style="font-size:10px">` sits 2 px high (1: a smaller inline font's
  baseline under the normal line height); `position:absolute` without
  offsets is placed at the container top instead of its static position
  (1: y 0 where Chrome has 18).
- **Trap — `rem` is not `em`.** `_decl_line_height_own_font_milli` tests
  `ends_with("em")` and must exclude `rem`, which still goes through the old
  factor parse.
- **4K lane (3840x2160, Vulkan on llvmpipe) fits in 8 GB:** 16 min 52 s,
  max RSS 4.5 GB for all 8 pages. Measured at this tip: overview 0.24, html
  2.77, css-layout 2.09, css-paint 2.47 (row 2.50), forms-media 1.96,
  animation 2.23 (row 2.63), evidence 0.15, tab-bar 0.05. The two lower rows
  were lowered. Run it with
  `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json … --width 3840
  --height 2160 --backend vulkan`.

## 2026-11-14 — matrix clusters: inline button baseline, max-content of mixed inline content, control UA font (169 -> 106 cells)

- **Cluster census at 169 cells / 290 ids (by root cause, largest first):**
  inline `<button>` position (about 44 cells: every `*/button` child cell and
  most `button/*` cells); non-replaced inline boxes taking `width` / `height`
  / `min-*` and vertical padding/border growing the line (about 20: `span/*`,
  `display:inline` cells); `td` parents (24 cells on two pages); controls
  inheriting the parent font (9); `td` with a non-`table-cell` display or
  out-of-flow position (9); flex column / column-reverse / wrapped-line
  stretch (18); `display:inline-flex` (10); `width: min-content |
  max-content` and `white-space: pre-wrap` (8); percentage / negative
  offsets (5).
- **Inline button.** A `<button>` is an inline-block WITH a text child, so the
  run loop's baseline-set test (`display == "inline" or child_count == 0`)
  skipped it and it stayed at the line top. It is now in the set and
  `inline_widget_baseline_from_top` gives its baseline: the LAST label
  line's (Chrome: a three-line 51 px button sits at the top of a 52 px
  line), the label block centred in the content box; an empty button aligns
  on its content-box bottom. Margins take part through the existing
  `margin_ts` / `margin_bs`.
- **Max-content.** `flex_item_max_content_width` (auto table columns,
  absolute / float / flex shrink-to-fit) now mirrors `intrinsic_text_width`
  for inline content: a collapsible space between pieces counts, `<br>` ends
  the measured line, replaced inline children use
  `inline_replaced_predicted_width`, text controls
  `text_control_auto_outer_w`.
- **Control font.** `font: -webkit-small-control` is a whole shorthand: the
  tag defaults for `button` / `input` / `select` reset family
  (`sans-serif`), weight and style, not only size and line height.
- **Trap — whole-pixel pieces drift.** `ab <button>cd</button> ef` in a `td`
  is 78 px where Chrome has 76.13: five pieces each rounded to a pixel. The
  matrix keeps `tt-td-button-w/-p` baselined for it.
- **Heading margins.** `h6` carried 26 px margins; 2.33em of its 10.72 px
  font is 24.98. The others were already right.
- **`html` catalog page (15.98%) by area, 900x760:** rows 124-219 are 10.8
  of the 15.98 points -- the article's `<header>` has
  `background: linear-gradient(120deg, #173b7a, #6d28d9)` and the CPU raster
  lane paints it FLAT (`#173b7a`): `fb_style_background_opacity_clip` only
  knows the two-colour vertical form (`background_gradient_from/to`), while
  an angled or N-stop gradient is carried as stop lists for the Draw IR
  lane. A paint defect, not geometry. Text rows 240-760 are about 4.6
  points (glyph raster differences); the rest 0.6. Element geometry inside
  the viewport matches Chrome; the first geometry delta on the page is the
  `h6` example at y = 4534 (fixed above), then `<q>` without quotation marks
  (10 px narrower) and a `tbody` 2 px low.
- **Trap — the geometry differ's default Chrome run has a 15 px scrollbar.**
  Without `GEOM_DIFF_CHROME_EXTRA_FLAGS="--hide-scrollbars
  --force-device-scale-factor=1"` every block on a page taller than the
  viewport reports `dw = 15` and the real deltas drown (357 "mismatches"
  against 162 with the flag).
- Specs: `inline_button_baseline_chrome159_spec`,
  `table_cell_max_content_inline_chrome159_spec`,
  `form_control_ua_font_reset_chrome159_spec`,
  `heading_ua_margins_chrome159_spec` (all in `test/01_unit/browser_engine`).
- Residue: `doc/08_tracking/bug/web_matrix_table_button_html_page_residue_2026-11-14.md`.
- **Trap — an atomic inline box keeps its edge spaces inside.**
  `inline_subtree_edge_is_space` follows an inline element's first / last
  text to find a space on the line; it must not be asked about an
  inline-block, button or replaced child (`ab<button> cd </button>ef` is as
  wide as `ab<button>cd</button>ef`). The call sites gate on
  `display == "inline"` and not replaced. `white-space: nowrap` still
  collapses (only `pre` keeps spaces), so a nowrap cell keeps the
  inter-inline space in max-content.
- **Trap — `max-width: <percent>` used to be N px.** Percentage min-/max-
  sizes are now the negative sentinel (like `width`) and resolve in
  `style_with_resolved_percent_min_max`; every clamp reader tests `> 0`, so an
  unresolved sentinel is `none`, which is what max-content needs. Resolve at
  EACH call site against that site's containing block (normal flow, inline
  atomic, float, abspos padding box, flex container); `layout_with_style`
  only maps a leftover sentinel to `none`. Resolving there against the box's
  own width was wrong everywhere it mattered: an inline input came out 16 px,
  a float 193 instead of 200, an abspos 193 instead of 210, and
  `td{max-width:10%}` (ignored by Chrome) shrank the cell to 13 px. A flex
  item also needs the clamp INSIDE distribution (`flex:1;max-width:25%` of
  400 is 100 / 300), not only on the final width.
- **Trap — a gradient row has two painters.** The CPU raster paints a typed
  `linear-gradient` in `fb_style_background_opacity_clip` (fb lane) AND the
  Draw IR engine2d ramp (`emu_draw_linear_gradient_stops`); a fix in one
  lane only is invisible or half-visible, so run each new spec row red first
  to learn which lane it hits. Corner keywords are box-dependent: the parser
  stores 1000 + the square angle and both lanes resolve it with
  `gradient_corner_dir_q16`. Interpolation is premultiplied; stop positions
  never decrease. Emit a ramp a ROW at a time (`draw_image`): one
  `draw_rect_filled` per colour run cost the catalog `html` page 120 s.
  (`parse_color("red")` was #dc3232 until 2026-11-15.) The corner codes
  (>= 1000) share the angle slot, so every real angle must be reduced to
  0..359 first (`3turn` painted as "to top left" until it was). Ramp
  positions multiply by 1000: keep them in i64 past ~1073 px.
- **Trap — a UA reset needs `inherit` to exist.** Resetting the control
  font exposed that NO font property resolved the `inherit` keyword
  (`font-family: inherit` stored the literal text; `font: inherit` cleared
  weight and style). It only looked right while controls inherited by
  default; `button, input { font: inherit }` (normalize, Tailwind preflight)
  would have rendered every control in the UA font. `Style.inherit_font_*`
  / `inherit_bold` / `inherit_italic` / `inherit_line_height_px` capture the
  PARENT's computed values in `inherit_from` and `inherit_style`; `font`,
  `font-family`, `font-size`, `font-weight`, `font-style` and `line-height`
  read them for `inherit`. Before adding any tag default that replaces an
  inherited value, check that `inherit` restores it.
- **Button baseline, any content.** With auto height the content fills the
  content box, so the last line's baseline is `h - border_b - pad_b -
  descent` whatever the content is (a label in `<b>`, `ab<br>cd`, an image).
  Only an explicit height needs the centring lead, and that path still looks
  for a direct text child.
- **Max-content, spaces.** One collapsible space counts between inline
  pieces wherever it sits: a whitespace-only text node (`<a>Edit</a>
  <a>Del</a>`), the end of the previous element's text (`<span>ab
  </span>cd`), or the start of the next (`inline_subtree_edge_is_space`).
  Text controls are clamped by min/max-width (`constrained_outer_width`)
  and atomic inline boxes carry their horizontal margins.
- **Trap — one colour parser, CSS Color 4 values.** `parse_color` and
  `parse_color_alpha` hand `rgb()` / `hsl()` and keywords to dom_color's
  `parse_color_value_checked`, alpha kept in every syntax. 0 means
  "transparent or invalid" to every caller, so an invalid value must be
  rejected (never read as 0 = black), and a colour longhand OR shorthand
  (`background`, `border*`, `outline`) holding a malformed colour function
  is dropped whole in `_decl_table_build_inner`. A shortcut keyword above the table (`red` = #dc3232 survived
  for months) silently repaints every page; pin new forms in
  `css_color_parse_chrome159_spec.spl` against `getComputedStyle`.
- **Trap — a collapsed cell's box overlaps its neighbour.** In
  `border-collapse: collapse` the tracks hold half of each shared border, so
  the cell box is laid out from `cell_x - (b+1)/2` to `cell_right + b/2`
  (layout_engine table loop) and paints its full border with the ordinary
  paint path. Moving the border paint instead of the box leaves the content
  one pixel off (seen and reverted). Column edges round half up in both
  `table_distribute_auto_columns` and the fixed split; probe a fraction
  >= .5 when pinning one, or floor passes too
  (`table_collapsed_border_paint_chrome159_spec.spl`).

## 2026-11-15 — lane parity: Draw IR gradients, cpu_simd vs Vulkan census, hardware Vulkan 4K

- **Draw IR angled / multi-stop linear gradients now match the fb raster
  bit for bit (opaque).**
  `emu_draw_linear_gradient_stops` (`engine2d/backend_emu.spl`) used the
  corner pixel CENTRES as the line ends (`(w-1)` span) and truncated alpha;
  it now uses the fb raster's mapping (integer Q16 sin/cos tables generated
  from `gradient_angle_sin_cos_q16`'s series -- this file is also the
  baremetal raster, so no `f64` -- line `|w sin a| + |h cos a|`, `t16 / 64`
  quantisation, rounded premultiplied alpha). Was 13-16 levels off on 10x10 /
  12x6 boxes. Spec: `test/01_unit/browser_engine/linear_gradient_angle_draw_ir_chrome159_spec.spl`
  (Chrome 159 rows for 45/135deg, `to bottom right` on 12x6, translucent
  stops, and a whole-box lane-parity row; 9/11 -> 11/11). Translucent stops
  stay up to 2 apart: the fb raster quantises alpha to 0..100 %.
- **The default top-to-bottom two-stop ramp changed on the Draw IR lane
  too** (it goes through the same primitive): row centres along the line
  instead of exact stops on the first/last row. That is what Chrome does --
  10x10 `#000 -> #fff` row 0: Chrome #0d0d0d, Draw IR #0d0d0d (was #000000).
  The fb raster keeps its endpoint-exact dithered painter
  (`mix_color_vertical_centered`), which is now the outlier: #000000 there,
  up to 21 off on 12x6, within 2 on 200x100 (AC-11 bounds it at 2, AC-12
  pins Chrome). AC-13 runs the primitive on a real `VulkanBackend`
  (llvmpipe): device readback equals the software reference pixel for pixel.
- **Trap: the catalog gate's `vulkan` lane never calls that function.**
  `simple_web_render_html_to_pixels_with_engine2d_backend` paints non-"text
  document" pages through the fb raster and presents them; only the Draw IR
  entry `simple_web_layout_render_html_pixels_engine2d` reaches
  `draw_gradient_rect_stops`. And that entry with `"vulkan"` resolved to
  `selected=cpu` in a probe -- read `Engine2dDrawIrAdvResult.selected_backend`
  before claiming a GPU ran. `feature_showcase.spl` is the place where the
  primitive runs on a real `VulkanBackend` (byte-identical, 38 primitives).
- **cpu_simd vs Vulkan (llvmpipe), 900x760: 62 pixels over all 8 pages**,
  all text ink: some glyphs one row lower on Vulkan; Chrome mismatch
  identical per page. FIXED the same day (see the next section). Record + 25 px repro:
  `doc/08_tracking/bug/web_vulkan_lane_control_text_one_row_past_clip_2026-11-15.md`.
- **Hardware Vulkan 4K (NVIDIA GB10, driver 580.173.02,
  `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/nvidia_icd.json`, strict
  backend):** runs. overview 0.24, html 1.67, css-layout 2.09, css-paint
  2.41, forms-media 1.96, animation 2.23, evidence 0.15, tab-bar 0.05 --
  identical to the llvmpipe rows. 932 s for 8 pages (llvmpipe 1012 s), max
  RSS 4.5 GB: the interpreted page pipeline dominates, not the device. Run
  with `--baseline <nonexistent>` so it is compared, not judged against the
  llvmpipe file. The RenderDoc layer still cannot load on this driver.
- **Perf note (superseded 2026-11-15):** the "54 s of 76 s" `font_atlas_pack_u32_to_u8`
  figure is stale. On tree `7b88ee7874a` with the same seed, forms-media renders
  in 13-17 s and the pack was 0.8-1.5 s (21 packs, ~60 ms each); the drop came
  from upstream source, not from the binary. 12 of those packs were full
  repacks caused by the atlas being wiped on every text-size change, fixed in
  `doc/08_tracking/bug/font_atlas_wiped_on_size_change_full_vulkan_repacks_2026-11-15.md`
  (12 -> 3 full packs). The opt-in `SIMPLE_VK_FONT_UPLOAD=u32` lane renders a
  DIFFERENT pixel sum (`2697956136642868` vs `2697697746427296`) and must not
  become the default until that is explained. Checked 2026-11-15: it is already
  so on base `b8b14272484`; disabling the #9435 `clipped-out` return leaves the
  u32 sum byte-identical, so that is NOT the cause; draining the deferred u32
  upload at once moves it only to `2697952473848308`, and this branch (atlas kept
  across sizes) gives `2697955134348331`: the lane depends on atlas layout and
  upload order. The gap is the sum-equivalent of ~15.4k black-to-white pixels
  (no framebuffer diff yet); cause open. RESOLVED: the deferred u32 copy
  declined under the compiled array ABI after the dispatch was recorded, so
  the lane drew no text; see
  `doc/08_tracking/bug/vulkan_font_u32_lane_draws_no_text_compiled_abi_2026-11-15.md`.
- Gradient paint cost, same seed: 300 x 900x100 120deg boxes 1.02 s -> 0.39 s
  wall (startup 0.24 s), RSS +4 MB; 6000 12x6 boxes 0.25 s -> 0.25 s, +5 MB
  (boxes under 1025 px skip the table; a table per box cost +87 MB).

## 2026-11-15 — transparent is a value, mitred border corners, `width:0`, column-reverse, border cascade, whitespace by computed display

- **Trap — 0 still means "unset" to the parsers; transparency is decided at
  the applier.** `_parse_color_delegated` keeps returning 0 for both
  `transparent` and garbage. Every applier that must *override* an earlier
  colour asks `_decl_transparent_color(raw)` (any top-level token with alpha
  0, functions kept whole by `_decl_top_level_tokens`), so
  `background:red;background:transparent`, `color:transparent` and
  `border-*-color:transparent` clear the earlier value instead of being
  ignored. Both paths need it: the declaration table appliers
  (`_decl_apply`) AND the dispatch fast path in `..._declarations.spl`
  (`color`, `outline`) — the review caught the fast path missing it.
  Alpha-0 hex (`#f000`, `#ff000000`) returns 0 too.
- **Trap — named colours inside shorthands never parsed.** `border:4px solid
  blue` painted nothing until `_shorthand_color_token` ran before the
  rgb/hsl/hash fallback in `parse_color_any`. Multi-value `border-color`
  takes 1-4 values (top right bottom left); a first-token-only parse
  painted a square instead of a triangle.
- **Mitre.** A corner pixel belongs to a side when
  `(2c+1)*side_w > (2r+1)*cross_w`; the exact diagonal pixel gets ONE
  premultiplied 50/50 mix (`mitre_mix_color`; Chrome #7f0080 for red/blue,
  #ff7f7f for red/transparent). Blending it once per side double-blends.
  Framebuffer twin `_fb_border_sides_mitred`, Draw IR twin
  `_engine2d_draw_ir_render_borders_mitred`; only taken when adjacent sides
  differ.
- **`width:0` is a set width.** `node_w == 0` used to mean auto, so a CSS
  triangle was full width and `width:0;white-space:nowrap` grew. The
  `width_zero` style flag (copied in `copy_from`, `style_with_width`,
  `style_with_height_without_grid_fields`; false whenever the final width is
  not 0, so `width:0;inline-size:50%` is 150) is honoured by the "is width
  set" tests in layout_engine, `constrained_outer_width` (its `< 1 -> 1`
  clamp made every zero box 1px -- the first cut missed it), floats, abspos
  and the flex sizing branches. `height:0` is still auto (48 sites; filed).
- **Text alpha.** `_fb_text_px` blends glyph pixels with alpha 1..254 in the
  5x7 bitmap lane; engine2d `SoftwareBackend.draw_text` blends via
  `sw_blend_const_raw_span`. TTF and other backends: open.
- **Unclosed function at the end of an inline style** (`color:rgb(0,255,0`)
  is closed by `_inline_style_closed` before the priority split (CSS
  Syntax: EOF closes open blocks).
- **Trap — whitespace is judged by COMPUTED display, never by tag.** The
  parser keeps a whitespace-only text node after any element as one space
  (never inside `<pre>`), and `compute_styles_with_material` hides it
  (display:none) inside flex/grid/table containers and beside a block-level
  sibling. The first cut kept it after "inline tags" and broke two catalog
  pages: forms-media (`label{display:block}` -> an extra line per control,
  6.37 -> 9.46) and tab-bar (a space flex item + two gaps between every
  button, 0.68 -> 2.00). Flex row/column and grid loops now skip
  display:none children (no item, no gap). Kept whitespace fixed the
  animation page's 4-9px shifts. Simple's space advance is 6px vs Chrome
  4.45 — open.
- **Trap — a shorthand must store its longhands at its own source
  position.** The appliers run in a fixed order, so
  `border-top-color:red;border-color:blue` stayed red until
  `_border_shorthand_longhands` (foundation, `_decl_table_build_inner`)
  started writing `border-*-color/width/style` entries right after the
  shorthand; the last-wins lookup then sees source order. A `border-color`
  with a non-colour token returns `["!"]` and drops the whole declaration.
  A shorthand also stores what it omits (width 3px, style none, color
  `currentcolor` -> the element colour): `border-top-style:dashed;border:2px
  red` paints nothing in Chrome. Logical properties (shorthands AND
  longhands) are stored as their physical longhands only (horizontal-tb
  ltr), so the fixed-order logical appliers never re-apply them; only a
  `var()` value still reaches them. Trap: the table used to be allocated at
  26 slots per declaration whenever the text held "border" (even
  `box-sizing:border-box`) and was never trimmed -- every lookup scanned
  the empty slots. It is cut to the used length now.
- **Trap -- abspos stretch tests must read "is set", not "> 0".**
  `left:0` and `inset:0` were never stretched because the test was
  `left_px > 0`; use `left_auto`. The rtl over-constraint rule applies only
  with a definite width and uses the containing block's direction.
- **Trap -- outline `auto` is not a border style.** `css_border_style_token`
  does not know it; `outline_shorthand_paint_width_px` is the one resolver
  for both appliers (omitted width = 3px, omitted style = no paint).
- **Trap -- `white_space_pre` means nowrap too.** It cannot carry
  `pre-wrap`/`pre-line`; a kept newline between elements uses
  `Style.white_space_newline` + `HNode.ws_raw` (`html_kept_newlines` counts
  them; extra newlines add line heights) and is laid out by the `<br>`
  branches (layout_engine, layout_foundation measure). A multi-space
  whitespace node is NOT collapsed by normal-mode layout, so the parser
  stores the space count only inside preformatted tags.
- **`flex-direction: column-reverse`** restacks bottom-up from the content
  bottom in DOM order with physical margins (reflecting the column result
  got asymmetric margins wrong: t=38 vs Chrome 42). Chrome 159:
  flex-start/normal/`end` pack at the bottom, flex-end and `start` (the
  physical top) at the top, center/space-* keep the reversed order. Move
  items with `offset_layout_subtree` by (target - flow y): `out_by` already
  holds the `position:relative` offset, so subtracting it from the box y
  instead dropped `top:10px`. Auto main margins and `order` are not
  modelled (filed). Next cluster: flex-wrap line stretch under a definite
  height (align-content stretch; Chrome items 45 tall, Simple 24).

## 2026-11-15 — Vulkan text clip: cpu_simd and Vulkan byte-identical

- Root cause of the 62 px: `VulkanBackend.composite_font_batch` (the
  vector-face path behind `draw_text_with_advances`) ignored `set_clip`; only
  the bitmap path baked the clip into its quads. Draw IR clips control text to
  its box, so descenders spilled below `<input>`/`<select>` on Vulkan only.
  Fixed by clipping the quads on the host; a fully clipped batch is the
  admitted status `clipped-out`. Record:
  `doc/08_tracking/bug/web_vulkan_lane_control_text_one_row_past_clip_2026-11-15.md`;
  RenderDoc params-buffer evidence in the simple_renderdoc skill.
- 900x760: all 8 catalog pages `cmp`-identical cpu_simd vs Vulkan (llvmpipe).
- `draw_ir_adv_branch_coverage_spec` hostile-advance row expected 8 skips,
  but the executor now paints such runs with the font's own advances
  (`text-advance-arity` fallback; no code emits `text-font-advances` any more,
  only a stale comment at `draw_ir_adv.spl:555`). Row re-pinned to 9 rendered /
  0 skipped plus a pixel row proving hostile advances paint exactly like no
  advances.
- `engine2d_software_offscreen_dispatch_spec` (0/3) asserts a software rung
  that `engine.spl` todo 303 says does not exist; filed, not edited:
  `doc/08_tracking/bug/engine2d_software_offscreen_dispatch_spec_asserts_missing_rung_2026-11-15.md`.
- Hosts without `/usr/share/vulkan/icd.d/lvp_icd.json` do NOT exercise the
  Vulkan rows of `vulkan_text_advances_clip_parity_spec` or AC-13 of
  `linear_gradient_angle_draw_ir_chrome159_spec`: each prints a
  `[skip] ... was not exercised` line and returns. Read the log, not the
  pass count, before citing them as Vulkan evidence.
- Draw IR advances are applied only when they sum to the command width;
  otherwise the run silently paints with the font's own advances. A test of
  "advances applied" must set the width to the sum (see the `7,7` row).

## 2026-11-15 — wrapped flex lines size their items; the headless shell is not the oracle

- **Trap — the gates must run FULL Chrome.** With no `CHROME_BIN`, the
  harvester (`check-chrome-layout-geometry-diff.shs --print-chrome`) prefers
  the Playwright headless shell, which resolves `monospace` to DejaVu Sans
  Mono through fontconfig: every `<code>` line box is 1px shorter and the
  matrix reports 28 NEW ids (127 cells) at an untouched base. Full Chrome
  (`CHROME_BIN=$HOME/.cache/ms-playwright/chromium-1255/chrome-linux-arm64/chrome
  CHROME_NO_SANDBOX=1`) gives the recorded 102. Never baseline those ids;
  cross-check any hand measurement of text from the headless shell.
- **Fonts on both sides (audit).** Simple's Linux face set is Liberation
  Sans / Serif / Mono (`browser_host_has_measured_linux_face_set`). Chrome is
  not handed that file: it resolves the generics through fontconfig to its
  Arial / Times New Roman / Courier New defaults, which this host aliases to
  the same Liberation files -- same face by host configuration only. The
  catalog uses 16px / 24px text and no `@font-face`; no fixture enlarges
  text to hide a mismatch. High-DPI comparison (owner rule: >= 300 dpi or a
  shared 1px bitmap font) is blocked on a device scale the renderer does not
  have: `doc/08_tracking/bug/web_render_no_device_scale_hidpi_gate_2026-11-15.md`.
- **Wrapped lines align their items.** The wrap branch placed each line at
  its align-content-stretched offset but laid every item out at content
  height. After the line loop, each in-flow item is aligned inside its line
  (CSS Flexbox 9.4 step 11): an auto-height `stretch` item (not replaced,
  no max-height, no auto cross margin) grows to the line's cross size, an
  `end`/`flex-end`/`center` item moves down by the free space
  (`offset_layout_subtree`). The line cross size is the larger of the
  stretched estimate and the tallest real item, and the next line starts
  below the REAL items (`line_heights` estimates an auto-height item as one
  line box, so `aa<br>bb` used to overlap the next line). `wrap-reverse`
  keeps the old placement. Matrix 102 -> 95 cells (21 `cc-fx-fw-wrap-*`
  ids). Spec: `flex_wrap_line_stretch_chrome159_spec.spl`.

## 2026-11-15 — `simple_web_renderer_spec` was red from a stale snapshot; the matrix gate picks full Chrome

- **Trap — a red main spec can be a lost harness, not a lost feature.**
  `88aac2ffe28` (release/1.0 transplant) replaced the spec with an older copy:
  five helpers, three rows, ten imports and the head of the content-visibility
  row vanished, so 9 rows died on `function/variable ... not found`. Before
  triaging a value, grep the spec for every `_helper(` it calls and diff the
  row against `88aac2ffe28^`. Restored: 111 -> 114 rows, 83 -> 92 passing;
  the 22 left are classed in
  `doc/08_tracking/bug/simple_web_renderer_spec_red_rows_2026-11-15.md`.
- **The matrix gate no longer takes the headless shell.** Without
  `CHROME_BIN` it uses a system Chrome, else the newest Playwright
  `chromium-*/chrome-linux*/chrome`; a headless shell (found or passed) is an
  ERROR naming the reason (`full_chrome_in`, `is_headless_shell`; selftest 11
  -> 14 fixtures). The geometry differ's own preference for the shell is
  unchanged.
- Batch 1 (`71ff31154d5`) catalog 900 px: every page equal to its row
  (worst css-paint 6.80); `html` 216.2 s vs 226.6 s at base, `css-layout`
  266.0 s vs 274.3 s, same seed.

### Batch 3a (2026-11-15): host-dependent renderer rows, numeric Playwright pick

- **Playwright build is picked by number, not by glob order.** Both the
  matrix gate (`full_chrome_in`) and the catalog gate
  (`newest_playwright_chrome`) parse the `chromium-<n>` build and keep the
  largest, so `chromium-999` can no longer shadow `chromium-1255`. Each gate's
  selftest has a 999/1255/1200 fixture expecting 1255.
- **A backend-name row is host-dependent, not a regression.** The resolver
  probes the real device and honestly falls back to `software`
  (`9970185d1de` surfaced the reason). Expect the canonical name only where an
  independent `Engine2D.probe_backend` initializes; check aliases with
  `backend_canonical_name`. On this aarch64 host: cuda/vulkan/cpu_simd
  initialize; hip, opencl and metal ("Metal requires macOS") do not.
- **Chrome pixel probe without ImageMagick:** screenshot with full Chrome,
  then load the PNG into a canvas in a second headless page
  (`--allow-file-access-from-files --disable-web-security`) and print
  `getImageData` through `--dump-dom`.
- **Chrome samples a vertical 2-stop ramp at row centres.** Measured
  2026-11-15, Chrome 159: a 4 px `#000 -> #fff` ramp gives 1F/60/9F/DF, and a
  16 px one gives 08 at the top row and F7 at the bottom. The CPU raster's
  endpoint-exact `mix_channel_gradient_centered` (t = pos/(span-1)) is wrong
  against this; Draw IR already samples centres (AC-12 in
  `linear_gradient_angle_draw_ir_chrome159_spec`).

### Batch 3b/3c (2026-11-15): opacity composite, paint order, ink rows

- **A group-opacity composite must honour the child's own alpha.**
  `engine2d_composite_region_milli` (`engine.spl`) blended the child at a
  constant alpha since `ece10b378c8`; with a full-viewport opacity layer every
  transparent pixel darkened the page (`0x807c7d7e`). Effective alpha is now
  `src_a * a8 / 255`.
- **Positioned z-auto boxes paint after in-flow content.** The Draw IR paint
  order (`_html_draw_ir_node_paint_order`) groups positioned boxes with
  `z-index >= 0` after their context's in-flow members.
- **8 px text has no exact-colour pixels in Chrome.** Assert ink, not the
  text colour, for small text; exact-colour counts only describe the 5x7
  bitmap face.
- **Never pair a probe with a create to gate a GPU row.** The GPU is shared;
  take name and reason from one `..._resolved_backend_name_with_reason` call.
- **Put a seed probe inside the worktree it tests** (e.g. an ignored
  `build/wr_probe/`): from a scratch dir, `std.*` can fail to resolve
  root ("resolves from the project stdlib roots only").
- **Old trees do not run on the current seed** (HIR lowering errors before
  ~2026-11-14), so find introducing commits from the code and `git log -S`.

## Gradient ramps (2026-11-15)

- **Chrome never paints a stop colour exactly on a vertical ramp.** It samples
  row centres, `t = (2*row+1)/(2*h)`, then dithers per device pixel with Skia's
  8x8 ordered matrix: `X = x`, `Y = y ^ x`, `M` interleaves the low 3 bits
  (`Y&1<<5 | X&1<<4 | Y&2<<2 | X&2<<1 | Y&4>>1 | X&4>>2`), stored
  `floor(v + (2M+1)/128)`. `gradient_dither_threshold` returns `M`.
- **Fit before porting.** Replay a candidate model in a scratch awk script
  against every Chrome pixel you have (`cpixel.shs`) and port only on an exact
  match. Pins that hit stop colours exactly were never Chrome values.
- Dither uses DEVICE coordinates; within one row only `x & 7` matters, so the
  painter computes 8 phase colours per row and merges equal runs.

## 2026-11-16 — min-width beats max-width

- **Order matters:** CSS 2.1 10.4 applies `max-width` first, then `min-width`, so `min-width` wins a conflict. `constrained_outer_width` (`..._layout_foundation.spl`) clamped in the opposite order, and the auto-margin centring clamp (`..._layout_engine.spl`) never consulted `min-width`. `width:50%;max-width:300px;min-width:500px` was 300 wide; Chrome 159 makes it 500.
- **Trap — running the gates by hand:** both Chrome gates need `SIMPLE_BIN` (seed path) and `CHROME_BIN` (full Chrome) in the environment; without them they print `ERROR — nothing was checked` and exit 2, which is easy to miss in a chained script.
- **Gates at the fix:** matrix 95/979 (no change), catalog 900 worst 6.80 (no change).

## 2026-11-16 — rem uses the root font-size

- **Root font is cascade state:** `css_cascade_root_font_set` is set to 16 at the start of `compute_styles_with_material`, set to the `html` node's computed `font_size` once that node is stored, and reset at pass end. Every `rem` reads it (`css_cascade_root_font_px()` in `..._decl_apply.spl`, `_css_cascade_root_font_px` in `..._declarations.spl`). The root's own `font-size:Nrem` still uses 16, which is the initial value.
- **Trap — two dispatchers:** `margin-left` is parsed in BOTH `_apply_decls_dispatch` (`..._declarations.spl`, fast path) and `_apply_decls_without_grid_inner` (`..._decl_apply.spl`). Fixing one leaves the spec red; grep both for any longhand you touch.

## 2026-11-16 — box-sizing:inherit

- **`inherit` on a non-inherited property** needs the parent's value carried on the child Style, as `inherit_font_size` is. `inherit_border_box` is set in `inherit_from`, copied in `copy_from`, and added to `inherited_digest`. Skip the digest and the cascade memo can hand a child the style computed under a different parent.
- **Trap — CSS braces in spec literals:** write `body{{margin:0}}`. A bare `{margin:0}` inside a `"..."` literal is interpolation and fails with `variable margin not found`; `{margin:0;font:...}` only happens to survive.

## 2026-11-16 — compound selectors in any order

- **One splitter, four consumers.** `_compound_base_tokens` feeds `parse_selector_part` (ParsedSel), `base_selector_matches` (text path, the debug oracle's other side), `selector_bucket_kind/value_from_base` (rule candidate buckets), and `_part_specificity`. If a bucket key is wrong, the rule is never a candidate. The matcher alone cannot show this: `.a#t` matched once parsed, but it sat in the `a#t` class bucket.

## 2026-11-16 — :first/last/only-of-type

- **A new structural pseudo-class needs SIX touch points** in `..._core_selectors.spl`: the `PSEUDO_*` code, `_pseudo_code_for`, the text-path allow-list in `simple_match` (the `pseudo != ...` chain), the text-path ctx branch, the parsed-path ctx branch, and `_option_needs_ctx` (without it, `:not(X)` is evaluated with no siblings). Miss the allow-list and the text path returns false while the parsed path matches; `web_selector_parsed_equivalence_spec` catches that.

## 2026-11-16 — absolute height stretch and margins

- **`absolute_containing_h` is the PADDING-box height** (`content_height_limit + pad_t + pad_b` at every call site), while `containing_w` is the CONTENT width and callers add the padding back. Mixing the two up gives the wrong stretch only when the parent has padding, so the spec includes a padded parent.
- Absolute boxes now take their margins in `absolute_child_x/y` and in the width stretch. Before this an abs box with `margin:1px` sat at the inset with no offset, which no catalog page exercised.
- **Trap — per-call-site variable names:** the five `absolute_child_style` call sites name the child `c`, `fc`, `fc_wrap` and `flex_c`. A blanket `nodes[c]` replace only fails with `variable c not found` when a flex absolute child is actually laid out. `layout_renderer_box_geometry_chrome159_spec` ("flex row/col abs child") caught it, and nothing at load time did.

## 2026-11-16 — absolute static position

- The static y of an auto-inset absolute box is `cy + prev_margin_b + margin-top`, not `cy`. The previous sibling's bottom margin is still pending in `prev_margin_b` (it has not been added to `cy` yet), and Chrome places the box after it.

## 2026-11-16 — percentage flex-basis

- A percentage that is only known at layout lives in its own Style field with default `-1` (`flex_basis_permille`), so none of the giant `Style(...)` constructors need editing. Only the decl_apply constructor passes it, and `copy_from` copies it. `flex_item_percent_style` (called at every ROW flex item site) resolves it into `flex_basis_px` and resets it to -1. The column path at the `flex_c` loop deliberately does not call it, so a column percent basis stays auto (it needs a definite height).

## 2026-11-16 — flex min-width freeze

- The §9.7 freeze loop for zero-basis items already existed. It keyed on `zero_floor_w` (the automatic minimum), which returned the bare frame when `min-width` was set. Making the floor the declared min-width was enough: no new loop.

## 2026-11-16 — column flex grow and shrink

- **The column path had no grow/shrink at all** (row-only Flexbox 9.7). `col_flex_target_heights` returns per-child outer targets in SIBLING order (-1 = untouched, empty = nothing to do), and the item loop indexes it with a `col_k` counter bumped on every child, absolute and `display:none` included. Keep the two loops walking the same `first_child`/`next_sibling` chain.
- **The natural-first rule** applies only to auto-height items with children: lay out once with the original style, and keep that result if it is at least the target. It costs a second layout only in that case. Explicit-height items take the target directly, which is what lets a 40px text item shrink to its line height.
- **The natural pass and floats:** `layout_with_style` APPENDS floats (`float_ctx_add`), while line boxes are indexed per node and get overwritten. So the second (target) layout first calls `float_ctx_truncate` back to the count from before the natural pass and restores `g_float_max_y1`.
- **Bail rather than guess:** an auto-height item with element children returns base -1 and the helper returns `[]` for the whole container, which keeps the old layout. A one-line estimate there made siblings shrink or grow wrongly (review finding), which is worse than doing nothing.
- **Perf:** the helper returns early unless the container has a height, max-height or min-height. Measured on `layout_renderer_box_geometry_chrome159_spec` with the seed 59635056 B (2026-11-14 09:32): 16.3 / 15.9 s and 428 MB on head vs 15.4 / 15.6 s and 428 MB on base.
- **Trap:** a merged Chrome oracle page shifts every y. Re-measure the COMBINED page, never add offsets by hand.

## 2026-11-16 — single-line row flex cross alignment

- The wrap path aligned items per line after layout, but the single-line path had no such pass: stretch, center and end there only used `st.height_px`. The fix is the wrap path's loop run once with `max_child_h` as the line. Stretch only raises `out_bh`, since block content stays at the top; center and end move the subtree with `offset_layout_subtree`.

## 2026-11-16 — background shorthand after the size group

- `_parse_background_shorthand` is a token state machine. `after_slash` must END at the first non-size token, or every box, attachment or colour keyword after `pos / size` fails the whole layer closed. Its regression partner is `layout_renderer_background_and_grid_decls_spec` "refuses a malformed position/size slash": `center / 1px 2px 3px` must stay invalid, which is why a position token after the slash returns empty.

## 2026-11-16 — text Draw IR line-height

- `_html_draw_ir_resolved_text_command` merges the resolved-font props over the CSS computed style. `line-height` must stay the CSS value (`style_line_h`); the face metric only stands in for `normal`, and `style_line_h` already answers that. Nothing in Engine2D reads the value, only its presence.
- Narrow Draw IR fixtures drop text that starts past the surface edge. Spans with no whitespace between them never wrap, so a fixture that once fit with bitmap metrics culls once real faces are wider. Widen the surface; don't relax the expect.

## 2026-11-16 — background-image longhand witness

- `bg_layers_raw` does double duty: it is the fail-closed witness (css-cascade spec), and Draw IR treats any non-empty value as "not lowerable". A lone exact `url()` longhand keeps its text there and must still lower: `_html_draw_ir_single_url_witness`. When adding a raw witness to a new branch in decl_apply, check `_html_draw_ir_background_layers` and the material gate (`raw_layers_empty`) in paint_layout.

## 2026-11-16 — raster-only paint is invisible

- The pixel API (`simple_web_render_html_to_pixels`) renders Draw IR through Engine2D. Anything painted only in `paint_raster.spl`'s `paint` never reaches it: the widget-image placeholder (now ported) and the widget panel, button and chrome-text fills (still open). When a pixel row shows only the page background, grep `paint_raster.spl` for the feature before debugging layout.

## 2026-11-16 — device-scale (>=300 dpi) render path

- Rule: Chrome-vs-Simple pixel checks run at >= 300 dpi (device scale >= 3.125); we use integer k=4 (384 dpi). Same font file on both sides; never enlarge CSS font sizes to pass.
- Entry: `simple_web_render_html_to_pixels_at_device_scale(html, css_w, css_h, k)` (simple_web_renderer.spl) -> `simple_web_layout_render_html_pixels_engine2d_at_device_scale` (simple_web_layout_engine2d_fast.spl). Layout and the document cache stay in CSS px; only the composed Draw IR is scaled, by `draw_ir_composition_at_device_scale` (src/lib/common/ui/draw_ir_device_scale.spl), then painted into a (css_w*k)x(css_h*k) target.
- Scaled: command x/y/w/h, border/content/hit/clip rects, embedding x/y/w/h, points, edge points, advance_widths, glyph-run xs/ys, fractional geometry, affine tx/ty; style props font-size, line-height, letter-/word-spacing, text-indent, stroke-width, outline-width/-offset, text-decoration-thickness, text-underline-offset, border-*-width, border-*radius, box-shadow-blur-radius, box-shadow-layer-N-{offset-x,offset-y,blur-radius,spread-radius}, background-tile-*/shape-*/radius-*, backdrop-filter-realized-blur-radius-px, the two px ints of legacy box-shadow/text-shadow, every entry of font-advance-widths. Text is re-rasterized at k x font-size (real outlines), not upscaled.
- NOT scaled, by design: colors, gradient stops (colors + permille positions), angles, counts, identities; raw CSS text (box-shadow-raw, backdrop-filter, background-layers-raw, box-geometry-raw-tokens) because Engine2D reads their scaled typed twins; layout INPUT props (width, margin-*, padding-*, left, background-size-*/position-*) because paint never reads them and they can hold sentinels.
- Known gap: the Engine2D linear-stroke path admits only stroke-width 1, so a scaled straight edge/path (stroke-width k) is skipped and the pixel entry returns []. Not exercised by the spec fixtures; fix before a gate page uses SVG/edge strokes.
- Measured (Chrome for Testing 159.0.8154.6 aarch64, `--headless --force-device-scale-factor=k`, tol 8, boxes + "Hello Simple" in DejaVu Sans 16px, both sides /usr/share/fonts/truetype/dejavu/DejaVuSans.ttf 759720 B): k=1 3.85% (770/20000), k=4 0.93% (2990/320000). Spec: test/01_unit/browser_engine/web_device_scale_spec.spl.

## 2026-11-16 — input text overflows and is clipped, never truncated

- `input_text_paint_plan(nd, st, x, y, w, h, ancestor_clip)` paints the WHOLE value (password: one `*` per codepoint) and relies on `plan.clip` (content box ∩ ancestor clip). There was a `content_w / advance + 1` glyph cap at five call sites; Chrome 159 keeps the full value (`scrollWidth` 56 in a 36px content box) and clips it. Do not reintroduce a cap to save glyph work: all three painters (raster TTF, raster bitmap, Engine2D `set_clip`) honour the clip.
- An overflowing value ignores `text-align` (CSS Text 3 §6.1): LTR starts at `content_x`, RTL ends at the content right edge. Buttons (`type=button/submit/reset`) still centre an overflowing label. That is a known divergence: Chrome 159 start-aligns it (a 40px submit with 2px padding and 12 Arial-8px `M`s paints ink from x=3 to x=41, past the content box, so it is clipped at the border box, not the content box). It is open for the owner.
- Chrome 159 gives `<input>` a default `box-sizing:border-box`, but the engine uses content-box. Author `box-sizing` explicitly in input oracle pages, or the content box differs before paint is even reached.
- Oracle: test/01_unit/browser_engine/input_text_overflow_clip_chrome159_spec.spl.

## 2026-11-16 — catalog gate `--device-scale K` (384-dpi lane)

- `sh scripts/check/check-chrome-catalog-pixel-diff.shs --device-scale 4` (integer >= 1, default 1 = old behaviour byte-for-byte). Chrome gets `--force-device-scale-factor=K` on both the viewport probe and the capture; `--window-size`/`innerHeight`/deficit stay CSS px (Chrome 159 fresh profile: deficit 200 at K=1 and K=4); differ crop is `--ref-viewport-rows H*K`; frames are 3600x3040 at K=4.
- Simple side: `examples/06_io/ui/web_render_page_ppm.spl` reads `PAGE_DEVICE_SCALE`; K=1 keeps the old entry, K>1 calls `simple_web_layout_render_html_pixels_engine2d_at_device_scale` with the backend resolved at DEVICE px (the public `simple_web_render_html_to_pixels_at_device_scale` hardcodes "auto", which would defeat `SIMPLE_2D_BACKEND_STRICT`). An empty frame at K>1 prints `error: device_scale=K render returned 0 px (skipped commands ...)` (the stroke-width>1 gap).
- Pipeline attribution: the at_device_scale path at K=1 is byte-identical (`cmp`) to the gate's K=1 PPM on tab-bar, so a K=1 vs K=4 delta is the dpi change, not a pipeline change.
- Fonts (Chrome canvas measureText, 40px probe): `sans-serif` = `Arial` = `"Liberation Sans"` (1133.926) != `"DejaVu Sans"` (1286.992); `monospace` = `"DejaVu Sans Mono"` (1444.922). Simple's font_provider uses the same two files. Do NOT use `fc-match sans-serif` (says DejaVu Sans) — Chrome resolves the generic via its Arial pref.
- Baseline: own file per scale, `chrome_catalog_pixel_diff_baseline.<host>[.<w>x<h>.<backend>].dprK.txt`; the 1x file is untouched.
- Measured K=1 -> K=4 mismatch_pct (baseline `chrome_catalog_pixel_diff_baseline.Linux-aarch64.dpr4.txt`): overview 2.88->1.49, html 5.25->3.74, css-layout 5.85->4.01, css-paint 6.80->4.49, forms-media 6.37->5.86, animation 6.75->4.14, evidence 1.72->0.58, tab-bar 0.68->0.54. All 8 pages render at K=4 (no stroke-gap empties).
- Cost (cpu_simd, interpreter, 2 lanes in parallel on a shared box): Simple 14.5-38.7 min per page at K=4 (evidence 14.5, tab-bar 17.3, overview 19.9, html 29.1, forms-media 36.8, css-paint 37.0, animation 37.3, css-layout 38.7) vs 0.4-5.4 min at K=1; Chrome <1 s. Full 8-page K=4 run ~2 h wall as two --pages halves (7508 s + 6398 s); serial would be ~3.8 h. Each K=4 PPM is 32.8 MB.

## 2026-11-16 — coverage lane on this tree + layout_core / input overlay specs

- Coverage lane (seed `08aba9746a813ee7…`): `SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<x>.sdn simple run <spec>`, then score with `coverage_module_report` (doc/10_metrics/gpu/render_coverage_2026-11-14.md). `simple spl-coverage module` itself no longer loads on release/1.0.0 `49e6a927ae8` (`error[E1002]: function friend not found`; dropping its `std.fs` import is enough to avoid it, `std.platform` was not isolated). A driver importing only `std.common.coverage_module_report` plus an `rt_file_read_text` extern gives the same numbers. `SIMPLE_COVERAGE=1 simple test` still fails with the child-APK receipt error.
- `layout_core.spl` went from 22.2% (18/81, 2026-11-14 sweep; 14/81 from its existing specs on this tree) to 96.2% (78/81) union. Spec: test/01_unit/browser_engine/layout_core_block_flex_chrome159_spec.spl, 12/15 green. The 3 red examples are Chrome 159 divergences in `_layout_block_be`: (1) `width` is used as the border-box width, not the content-box width; (2) adjoining sibling margins are added (25) instead of collapsed (15); (3) a bordered 300px parent gets a 290px content width.
- `input_text_source_byte_at_x` was never called by any spec, and the overlay branches of `input_text_paint_plan_with_overlay` were also unreached. Spec: test/01_unit/browser_engine/input_text_overlay_plan_contract_spec.spl, 12/13 green, expectations from the overlay contract. It found one divergence (red): for a focus byte that is not a boundary, scrolling resolves focus to the end, but the caret x uses byte-not-found = 0, so the caret is painted at the value start.
- 2026-11-16 `layout_core.spl` `_layout_block_be`: explicit `width`/`height` are content-box unless `StyleProps.box_sizing == "border-box"` (new field, `set_style("box-sizing")`); sibling vertical margins collapse in block flow only (never for flex, incl. column flex which reuses this fn); `layout_core_block_flex_chrome159_spec` 12/15 -> 15/15. `layout.spl` `_layout_block_node` (layout_tree path) still adds margins and treats width as border box.
- 2026-11-16 `layout.spl` `_layout_block_node` (the `layout_tree` path behind `browser_renderer` and `engine_merge`) now follows the same box model as `_layout_block_be`: content-box `width`/`height` (border-box floored at the insets, content height >= 0), sibling margin collapse in block flow only, and a bordered parent keeps its content width. Porting trap: `_layout_block_node` places the child at the `y` it is given (it does not add its own `margin-top`), so pass `cursor + gap` directly — copying layout_core's `cursor + gap - margin_top` lands the second box 15px too high. Spec: test/01_unit/browser_engine/layout_block_node_chrome159_spec.spl (base 2/7, head 7/7). Still open there: horizontal margins (case a), `display:none` children (case f).
- 2026-11-16 `layout.spl` `_layout_block_node` second pass: the PARENT loop applies a child's horizontal margins (passes x = content x + `margin-left`, avail = content width - both margins, clamped at 0), mirroring how it already applies `margin-top`, so the layout root's own margins stay unapplied; `display:none` children are skipped before margin bookkeeping so siblings around them still collapse (Chrome 159: f-collapse y=35). `layout_block_node_chrome159_spec` 7/12 -> 12/12. Open: `margin:auto` (parses to 0, no auto flag), parent/child collapse, `display:none` root.

## 2026-11-16 — K=4 paint cost: extern span calls copied the whole frame per row

- Cause: the software backend's span primitives (`sw_fill_raw_span`, `sw_copy_raw_span`, `sw_blend_const_raw_span`, the native branch of `draw_image_blend`) handed `self.buf` to an extern (`rt_engine2d_simd_*_span_u32`) or to `simd_span_batch_execute` (`var work_buf = self.buf`, then the first store forces a copy-on-write). Under the interpreter every such call unpacks and repacks the WHOLE framebuffer (`unpack_u32_array`/`pack_u32_array` in the seed's `interpreter_extern/simd.rs`). One call per scanline gives O(rows x surface), about k^3: 64x at K=4 for a 16x pixel increase. Hit by `clear()`, every opaque/alpha fill, every glyph-quad row, the shadow `draw_image`, and the host-memory writeback `engine.draw_image(0,0,W,H,read_pixels())` (3040 rows x 2 whole-array copies).
- Fix (pure Simple, `backend_software.spl`): `sw_span_scratch(offset, count)` copies only the span out; the SAME kernel runs on it; `self.buf.write_span(...)` writes it back in place. Copy spans call `write_span` directly. `simd_isa_fill_const` replaced its per-pixel store loop with one `dst.write_span(row, ...)`. `record_simd_*_hit` and `simd_batch_hits` accounting is unchanged.
- Byte identity and timing were measured on the interpreter lane only, which is the lane the gate uses. The effect on native/JIT lanes is unmeasured. There the extern already worked in place, so the scratch path only adds an O(span) copy per call. `record_simd_copy_hit()` now counts a `write_span` copy, not SIMD execution.
- Byte identity: `cmp` was identical, base vs fix, for tab-bar K=4, evidence K=4 and tab-bar K=1. Spec failures are identical on base and branch (same test names): simple_web_renderer 112/114, simple_web_engine2d_renderer 14/21, web_device_scale 7/7, backend_software_simd 10/14, backend_software_kernel_table_bucket 20/20. On the branch only: simd_provider 10/10 and simd_isa_provider 24/24.
- Measured (seed `/home/yoon/.cache/cargo-target-webrender-vk/release/simple`, 59635056 B, 2026-11-14 09:32; cpu_simd, interpreter, aarch64 host, MemoryMax=8G, one job at a time). On aarch64 the font path reports `cpu_simd:no-native-alpha-hit`, because its winner check requires `active_arch_text() == "x86_64"`:

  | page | K | before wall / RSS | after wall / RSS |
  |---|---|---|---|
  | tab-bar | 1 | 21.3 s / 0.81 GB | 7.9 s / 0.75 GB |
  | tab-bar | 4 | 839 s / 5.02 GB | 91.6 s / 2.93 GB |
  | evidence | 4 | 1153 s / 5.12 GB | 245 s / 2.88 GB |

  Phases for tab-bar at K=4, before -> after: document (parse, style, layout, compose) 0.46 s -> 0.46 s; device-scale pass 0.04 s -> 0.04 s; paint 810 s -> 69 s; PPM encode 27 s -> 21 s. Phase lines come from `SIMPLE_WEB_PHASE_TRACE=1`, which also covers the at_device_scale entry.
- Remaining cost: interpreter per-pixel work (the box-shadow loop, 64 px glyph raster, the PPM encoder). See `doc/08_tracking/bug/web_render_dpr4_residual_per_pixel_cost_2026-11-16.md`.

## 2026-11-16 — select UA background, native vs styled

- Chrome 159 computes `background-color: ButtonFace` (`rgb(239,239,239)`) for every `<select>`, but paints it only when the author styles the box: any `border*` (radius alone counts), `background*`, `box-shadow` or non-`auto` `appearance`. Otherwise the native menulist paints a WHITE field. `padding`, `color` and `font-size` do not count. A listbox (`multiple`, or `size` > 1) is a white `Field` either way. The UA fill is in `form_control_ua_box_decls`; the native white is the cascade tail's `_select_author_styled` check (`..._core.spl`). Spec: `select_ua_background_chrome159_spec`. forms-media 6.37 -> 6.08 at 1x.
- **Trap — computed value is not painted value for `appearance:auto` controls.** `getComputedStyle` says ButtonFace on the unstyled select too; only a `--screenshot` pixel shows the white. Pin control colours from pixels, not from computed style.
- **Trap — Chrome's catalog screenshots use LCD subpixel text AA** (colour fringes, e.g. `f0ce8c`/`6ec0f2` next to a `#172033` stem); Engine2D is grayscale. On forms-media the list text bands are about 70 % of the remaining mismatch with geometry aligned to <= 1 px. Before chasing a text band, sample a few pixels: coloured fringes mean AA mode, not layout. Changing the gate's Chrome flags (`--disable-lcd-text`) would rebase every row and is an owner decision. **Superseded 2026-11-16:** the owner chose to implement LCD text in Simple; see the LCD section below.
- Method that found it: a tile map (50x20 px mismatch counts) plus per-row ink profiles of the two frames. Rows aligned within a pixel ruled out layout; the remaining non-text tiles were the select.
- Gates at the fix: matrix 979 cells, 88 mismatching (no change, geometry-only gate); catalog 1x worst 6.80 (css-paint), every row unchanged except forms-media 6.37 -> 6.08 (baseline lowered).
- 2026-11-16 `layout.spl` `_layout_block_node` third pass: `margin:auto` via `StyleProps.margin_left_auto`/`margin_right_auto` (set by the longhands and every `margin` shorthand form; the f64 stays 0.0) resolved in the PARENT loop by `_used_horizontal_margins` (CSS 2.2 §10.3.3: explicit width only, split/one-side/over-constrained -> 0), and a `display:none` layout root returns a 0x0 childless box. `layout_block_node_chrome159_spec` 16/22 -> 22/22. Trap: `width` 0 means auto, so `width:0`/percent widths never centre. Open: parent/child collapse, root's own margins.
- 2026-11-16 `layout.spl` `_layout_block_node` fourth pass: parent/child margin collapse (CSS 2.2 §8.3.1) from DOM-derived margin SETS `[max_pos, min_neg]` (`_top_margin_set`/`_bottom_margin_set`), never pairwise `collapse(a, collapse(b, c))` (10/-5/3 must give 5); a private `bfc_root` param carries container-only BFC facts (layout root, flex/grid items); trap: Chrome `overflow:clip` is NOT a BFC root, it still collapses. Spec cases wrap the parent in a style-less root mirroring a `display:flow-root` Chrome wrapper.

## 2026-11-16 — WM material alpha is per-mille opacity on every backend; widget chrome text on Draw IR

- **WM material alpha (`wm-material-surface-alpha-milli`).** The CPU twin, Metal and Vulkan all read it as opacity: alpha `255 * milli / 1000`, straight-alpha src-over, result copied in place. The files are `draw_ir_glass_material.spl:222`, `backend_metal_msl.spl:361,373` and `shaders/glass_material.comp:146`, plus `backend_vulkan.spl:2857` `VK_IMAGE_COMPOSITE_COPY`. It is read once, backend-neutrally, at `draw_ir_adv.spl:805`, so there is no per-backend value to emit. 0.80 → 800. The old 200 oracle was 1000 - 800, which no consumer reads. On lavapipe it paints a 20 % surface (0xFFD2D2D2 instead of 0xFF4B4B4D).
- **Trap: a spec value that disagrees with its sibling field is the tell.** The row's own `background-color` carried alpha 0xCC, so 800 was the only value consistent with it.
- **Vulkan device proof recipe:** `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json`, `simple_web_render_html_to_pixels_with_resolved_engine2d_backend(html, w, h, "vulkan")`, then `vulkan_device_glass_material_count()` (reset with `vulkan_device_material_census_reset()`). Compare against `"cpu_simd"`. Rows are in `backend_vulkan_device_glass_blur_spec`. Metal stays static analysis on Linux.
- **Legacy widget chrome text on Draw IR.** `simple_web_layout_uses_legacy_widget_chrome` pages now get the F5F5F5 base (`_simple_web_layout_canvas_base`) and the generated chrome-text table (`generated_widget_chrome_text_pixels`). The Draw IR producer emits the table as `widget-chrome-text-<k>` 1x1 rects, gated by `widget_chrome_text_active`, and skips `#text` nodes under that gate. The raster uses the same three helpers. The frame rects, the sparse +8/+7 text and the background skipping are still raster-only.
- **Trap: in widget mode an empty `widget-panel` section fills the viewport height in Draw IR layout.** Text after it is off screen, so put a fixture's non-widget text before the panel.
- Gates at the fix: matrix 979 cells, 88 mismatching (no change); catalog 1x worst 6.80 (no change). Specs, base -> branch, same failing names otherwise: `simple_web_renderer_spec` 112/114 -> 116/116 (2 new rows); `simple_web_engine2d_renderer_spec` 14/21 = 14/21; `browser_renderer_spec` 130/131 = 130/131; `simple_web_html_layout_renderer_coverage_spec` 36/39 = 36/39; `paint_layout_coverage_closure_spec` 52/52; `paint_primitives_coverage_closure_spec` 26/26; `web_draw_ir_clip_cache_contract_spec` 1/2 = 1/2; `backend_vulkan_device_glass_blur_spec` 9/9 (2 new rows, lavapipe).
- Reach of the gate, checked 2026-11-16: `simple_web_layout_uses_legacy_widget_chrome` is `widget-panel` with no `<style` tag. No real producer hits it. `ios_css.spl`, `glass_css_components.spl` and `ui.web/html_css.spl` emit CSS only, and `glass_debug.spl` emits a text tree. `ui.render/html_widgets.spl` emits fragments that `ui.render/html.spl` / `ui.web/html.spl` wrap in a document with `<style>`. `glass_test_page.spl` carries `<style`. `widget_to_dom.spl` builds a DOM rendered through `render_dom_to_pixels`, not through the HTML gate. Only test fixtures reach it. The WM/widget specs (`theme_package`, `glass_css_backdrop_admission`, `widget_draw_ir_theme`, `glass_debug_interface`, `glass_css_output`, `dom_build_gpu_offload`) fail the same names on base and branch.
## 2026-11-16 — four owner-approved form-control / RTL behaviours ("all same as chrome")

Owner decision 2026-11-16: password mask, overflowing button label, RTL Latin order and the `<input>` UA `box-sizing` all follow Chrome 159. Each has its own `*_chrome159_spec.spl` with a Vulkan (lavapipe) device-readback row that asserts `resolved == "vulkan"` and `source == "device_readback"` before comparing pixels.

- **Password mask = U+2022.** `INPUT_PASSWORD_MASK_GLYPH` in `..._paint_raster.spl`. **Trap — the shared 5x7 table is the glyph source for BOTH the browser raster and Engine2D.** A non-ASCII mark needs a new packed cell AND a `glyph_index_for_char_code` arm; `FONT_CHARSET` stays ASCII (it is byte-indexed by `host_web`/`host_tui`/`cross_app_glyph_capture`). Appending a cell moves the Engine2D atlas unknown slot (`glyph_atlas_unknown_index`, now 89). The Vulkan bitmap-font atlas covers only ASCII 32..126 and rejects a run with anything else, so a bullet goes through the shared raster on that lane. Spec: `input_password_mask_chrome159_spec` (base 0/5, head 5/5).
- **Oracle trap — headless `--screenshot` stopped painting part-way down several pages** (everything below y≈52 was blank, even with `--virtual-time-budget`). Put every probed row near y=0, add a coloured sentinel box at the bottom and check it is painted before trusting a band. Pixels can be read back with Chrome itself: load the PNG into a canvas with `--allow-file-access-from-files`, then `getImageData`.
- **Overflowing button label = start edge, padding-box clip.** In `input_text_paint_plan` (`..._paint_raster.spl`), `type=submit|button|reset` labels are centred only when they fit. An overflowing label uses the text-value rule (content x, or content right minus width under RTL) and is clipped at the padding box. Chrome inks 3..28 in a 30px/1px-border/2px-padding button: into the padding, never into the border. Spec: `input_button_label_overflow_chrome159_spec` (base 0/6, head 6/6).
- **RTL = bidi visual order, not glyph reversal.** `bidi_visual_text_for_rtl` (`..._paint_primitives.spl`) replaced `reverse_text_for_paint` at every paint/metric site. **Trap — the `core.spl` advance-metric table must use the SAME visual string as the painters**, or a reordered glyph takes its neighbour's fractional advance. `input_text_visual_map` mirrors carets only when the text has a strong RTL character. **Trap — div text differs between the legacy software raster and the Engine2D path** (440 px on a 96x64 page, unrelated to direction), so a Vulkan row compares the device frame with `simple_web_render_html_to_pixels`, not with the software raster. Spec: `direction_rtl_bidi_order_chrome159_spec` (base 1/6, head 6/6).
- **`<input>` UA `box-sizing: border-box`** (all types but `image`/`hidden`) is one UA declaration in `form_control_ua_box_decls` (`..._core.spl`). It goes ahead of author declarations, so `box-sizing:content-box` still wins. Layout already honoured `st.border_box` for explicit control sizes, and an auto-sized input stays 185x21. **Re-pin rule (coordinator, 2026-11-16):** when a behaviour change moves an existing row, pin the EXACT new engine value with Chrome's measurement in a comment beside it. Never loosen a check to a range or a relation; a Chrome-closeness check can only be an extra assertion. Spec: `input_ua_box_sizing_chrome159_spec` (base 3/7, head 7/7).
- Gates after all four behaviours (2026-11-16, Chrome 159.0.8154.6, seed `cargo-target-webrender-vk`): matrix 979 cells, 88 mismatching (no change; the matrix has no form-control-only cells that these touch). Catalog 1x PASS, worst 6.80 (css-paint); forms-media 6.08 (no change); animation 6.75 -> 6.68 (baseline lowered; not attributed, since the base catalog was not re-run); every other row unchanged. Regression base -> head over 26 specs: 0 head-only failures.
## 2026-11-16 — LCD subpixel text (Chrome 159 LCD16) on the CPU lanes

Owner decision: implement LCD text in Simple; Chrome's flags stay as they are. Setting `SIMPLE_WEB_LCD_TEXT` (`engine2d_draw_ir_lcd_text_enabled`, `draw_ir_adv.spl`) defaults to on, like Chrome. `SIMPLE_WEB_LCD_TEXT=0` gives grayscale.

Measured Chrome behaviour (probed with `--headless=new --disable-gpu`, one `l` per page):
- **Mask.** Skia LCD16, 5 bits per channel, RGB order left to right. Black on white is always `255 - 8k`.
- **Blend.** `d + (((src - d) * s32) >> 5)`, where `s5 = cov >> 3` and `s32 = s5 + (s5 >> 4)`.
- **FIR.** A joint fit over four phases (48 subpixel samples) gives `[0.090, 0.225, 0.370, 0.225, 0.090]`, RMS 0.33/32. FreeType's default filter fits at 0.91/32 and Skia's gaussian at 0.50/32.
- **Size.** LCD when the DEVICE size is 48 px or less, grayscale from 49 px. At dpr4, 12px CSS text is LCD and 16px CSS text (64 device px) is grayscale.
- **Layers.** `will-change:transform` gives grayscale. `opacity` and `rotate` keep LCD.
- **Quarter-pixel phases.** Glyph pens snap to a quarter pixel: 1/3 becomes 1/4, 2/3 becomes 3/4. Left 1/1.25/1.5/1.75 px gives `ffe7b7 5f1f07 2f77cf f7ffff` / `ffffdf a74f17 0f3f97 d7f7ff` / `fffff7 d78f3f 0f174f a7e7ff` / `ffffff efc777 2f0f1f 67bfef`.
- **Mask gamma (preblend).** Light text gets thicker coverage per channel. Same glyphs, white on black vs black on white, step 2 becomes 3, 8 becomes 10.5, 17 becomes 19, out of 32. This is modelled as `cov^(1 - 0.22 * L/255)` per text-colour channel L.

Code path:
- `sfnt_render_glyph_lcd` (`sfnt_glyf.spl`) builds a 3x horizontal exact-span raster with 4 rows, then the FIR.
- `FontRenderer._lcd_glyph` produces atlas cells `(avg<<24)|(r<<16)|(g<<8)|b`.
- `_lcd_apply_pen_phases` swaps a quad to a phase cell (glyph_index `-1 - phase`) when the exact milli pen (`_text_pen_milli`, shared with `measure_text_advances`) rounds to a non-zero quarter.
- `engine2d_lcd_quad_composite` (`engine.spl`) applies the preblend tables and the Skia blend on an opaque destination. A non-opaque destination falls back to the grayscale blend.
- `_lcd_text_active` admits `cpu`/`cpu_simd`/`software` and, since 2026-11-17, `vulkan` (below).
- Spec: `test/01_unit/browser_engine/lcd_subpixel_text_chrome159_spec.spl` (AC-1..5 CPU, AC-6..7 Vulkan device).

### Vulkan LCD (2026-11-17)

The packed font kernel (`shaders/font_atlas_batch.comp`, blob `backend_vulkan_font_spirv.spl`, pin `check-font-atlas-batch-spirv-pinned.shs`) now has an LCD branch that reproduces `engine2d_lcd_quad_composite` byte for byte. Facts a maintainer needs:
- **Decision is per QUAD, like the CPU.** LCD math only if the quad holds an LCD cell (host scan, `_vulkan_font_quad_has_lcd_cell`) AND every destination pixel of the quad is opaque and on the surface (kernel gate). Otherwise the whole quad takes the old gray "over" blend. Inside an LCD quad a GRAY cell (rgb 0xFFFFFF) is blended through the s32 tables with cr = cg = cb = alpha, NOT through the over blend.
- **One workgroup per quad.** The opacity gate needs the whole quad, so an LCD batch dispatches X = 1 (the kernel strides over the quad's pixels); gray batches keep one group per 64 pixels.
- **Tables travel in the params buffer, not a 4th binding.** The seed fixes the pipeline layout at bindings 0..2 (`interpreter_extern/gpu.rs` ~5054). The glyph record stays 7 words (Metal parity, `VULKAN_FONT_PACKED_MAX_BYTES == 114720`). Header word 7 bit 31 marks an opt-in trailer after the glyph records: `G` table indices (0xFFFFFFFF = no LCD) then one 768-word s32 table per distinct LCD text colour (cap 32; more is refused, not drawn gray). Tables come from `engine2d_lcd_s32_tables` (`helpers/lcd_s32_tables.spl`, moved out of `engine.spl`, not duplicated). The pooled params buffers are `VULKAN_FONT_PACKED_POOL_BYTES` (max + trailer).
- **Trap: the 5x7 bitmap atlas has rgb = 0**, which the LCD-cell test would read as "LCD cell, zero coverage" and blank the text. The packer skips LCD for `VULKAN_BITMAP_FONT_CONFIG_IDENTITY` batches.
- **Trap: clip trimming hides surface overhang.** Draw IR clips each text box, so `vulkan_bitmap_text_clip_quads` bakes the clip into the quad and the kernel only sees the on-surface part. The CPU reads the UNTRIMMED quad back (off-surface reads as 0, not opaque) and paints an overhanging quad (a glyph at x=0 or flush right, because LCD padding reaches 1 px out) gray. `vulkan_font_lcd_veto_keys` records those trimmed quads on `VulkanBackend.font_lcd_veto_keys` and the packer draws them gray. Without it a page with margin:0 text differs on the first/last glyph.
- **`runtime-glsl` keeps the legacy layout.** The packer only emits the trailer and the X = 1 grid when `pipeline.artifact_mode == "precompiled-spirv"`; the common gray GLSL has no stride loop and would draw 64 pixels per glyph.
- **Cost:** LCD on Vulkan is about 60 % slower steady (cold several times) than gray on a 900x760 text page; gray is unchanged within ~5 %. See the bug record, open items 5-6, for numbers and an unexplained RSS drop.
- Reference for device parity is `simple_web_render_html_to_pixels` (default backend) or `cpu_simd` on vector-font pages; `cpu_simd` on 8px Arial form-control pages takes the bitmap lane and differs from Vulkan with LCD off too.

Gates and remaining gaps:
- Catalog 1x went from 2.88/5.25/5.85/6.80/6.08/6.75/1.72/0.68 to 2.53/5.14/4.74/5.68/5.17/4.93/1.07/0.71 (overview, html, css-layout, css-paint, forms-media, animation, evidence, tab-bar).
- tab-bar is +0.03 against a base rerun of 0.68; its row was not raised. The cause is geometry, not the mask. Centred white tab labels sit about 3/4 px right of Chrome, because only the run-relative fraction is phased and a fractional run ORIGIN is still snapped. Chrome also snaps horizontal strokes to whole rows (vertical hinting) and we do not.
- **Trap — div-only pages never reach this path.** Only pages that `_simple_web_engine2d_text_document` admits (`<p`, `<span`, `<h1`, ...) use Draw IR to Engine2D. A `<div>`-only probe page renders through the software raster and shows no LCD at all. Chrome paints `<p>` and `<div>` identically, so probe with `<p>`.
- **Trap — `simple run` of a scratch render script OOMs at 8G**, on base too. Run renders through `simple test` with a scratch spec.
- Catalog 4x, run on two pages only: forms-media 5.86 -> 5.56 (row lowered); tab-bar 0.54 -> 0.54. Its 16 px CSS text is 64 device px, so it stays grayscale.
- **Two assertions encoded grayscale AA, and Chrome's own pixels failed them.** Both are re-pinned (2026-11-17, owner: same as Chrome) to exact engine values at the same strength, with the Chrome value beside each:
  - `simple_web_renderer_spec` "uses explicit line-height for wrapped text layout" expected at least one pixel exactly `#0f172a` in 8 px text. Chrome's screenshot of the same HTML has 0 such pixels, because LCD coverage never saturates all three channels on a 1 px stem. It now pins the engine's darkest ink, `0xFF352A44` x 2 (Chrome: `0xFF4B3E5A` x 1). The y=42 `.after` line-height check is unchanged.
  - `web_device_scale_spec` "re-rasterizes text at k x font-size" expected 4x ink > 10 x 1x ink. It now pins the ink counts exactly: 1x 190, 4x 1629, i.e. 8.6x (Chrome: 199 and 1640, i.e. 8.2x). LCD fringes widen the 1x ink. The non-uniform 4x4 block check is kept.
- Perf: the first LCD commit was 45-51 % slower. After optimising the composite (s32 tables per colour, LCD before the gray subrect, empty and solid fast paths) and adding an O(1) atlas slot hint for phase cells: 1x 3.22 -> 3.52 s (+9 %), 4x 26.6 -> 30.4 s (+14 %). Frame digests are byte-identical to the first LCD commit. The remainder is the interpreted per-pixel blend; see `doc/08_tracking/bug/lcd_text_cpu_composite_44pct_slower_2026-11-17.md`.
- Combo matrix: 979 cells, 88 mismatching. Unchanged; it is a geometry gate.

## 2026-11-17 — css-paint residual classified (no fix)

- css-paint 5.68% = 38,905 px: ~75% glyph residual (LCD, vertical hinting, pen phase; excluded), 16.7% vertical drift (everything below the h3 sits 1 row low), ~7% the 18.72px h3 (integer font-size, 5 px wide), ~0.4% box edges. Table and fix sketch: `doc/08_tracking/bug/web_render_css_paint_residual_2026-11-17.md`.
- **Trap — a 1-row text offset on a plain `<p>` is not a baseline bug.** A probe page of `<p>` blocks matches Chrome ink rows exactly at 12/16/20/24 px; the drift comes from em margins (0.83em, 1em) and line-height 28.08 rounded box by box in i32 layout (Chrome 331.33 vs Simple 332). Do not touch the glyph baseline; carry a fractional margin remainder through the block cursor instead (all block-flow paths together).
- **Trap — `--dump-dom` without `--hide-scrollbars` lays out 15 px narrower.** Use only the y column of such a run.

## 2026-11-17 — flex-row main axis keeps fractions; edges are snapped

- **Trap — a row of `<button>` flex items drifted right one pixel per item.** `form_control_label_width_px` (layout_foundation) rounds each label UP, so tab-bar buttons were 74/55/90/80/109/78 wide against Chrome's 73.55/54.30/89.13/79.5/108.36/77.28, and by the 7th the left edge was 582 vs Chrome 578.
- Fix: `form_control_label_width_milli_px` measures the label unrounded (1/36 px oversample, floored to LayoutUnit 1/64), `form_control_button_frac_delta_milli_px` is the gap to the whole-px width, and the row loop in `layout_engine` (`frac_adj_milli`) snaps EDGES: `left = round(x)`, `right = round(x + w)`, `width = right - left`. The whole-px chain `cx` is unchanged, so only flex-row main-axis drawing positions move; block axis, wrap rows, reversed rows and the font renderer are untouched.
- Chrome 159 tab-bar (900 wide) snapped x,w: 48,74 130,54 192,89 289,79 376,109 493,77 578,73. Pinned in `flex_row_fractional_positions_chrome159_spec`.
- **Trap — the snapped width is NOT `round(w)`.** `289 + 79.5` is 368.47, so the 4th button is 79 wide, not 80. Always `round(right) - round(left)`.
- **Trap — oversample resolution matters.** At 1/30 px the four-label error (+0.03 px) pushed button 5's left from 376.47 over the .5 boundary to 377; 1/36 px plus a floor to 1/64 keeps it at 376.

## 2026-11-17 — Legacy widget frame rects and offset text on Draw IR

- **One rect list, two consumers.** `WidgetChromeRects` (`paint_primitives.spl`) is the shared shape for the legacy widget overlays. The raster writes it with `fb_widget_chrome_rects`; Draw IR lowers it with `_html_draw_ir_widget_rect_commands` (`paint_layout.spl`). Generators: `widget_frame_rects` (prefix `widget-frame-<k>`) and `widget_offset_text_node_rects` (`paint_raster.spl`, prefix `widget-offset-text-<k>`), built from `sparse_text_rects` and `text_decoration_rects`. The inline raster branches and `fb_glyph_sparse` are gone.
- **Paint order is the trap.** The raster paints every box, then the frame, then node text. Draw IR interleaves box and text per node, so in widget mode it skips every `#text` run in the node loop and emits frame, then offset text (document order), then the chrome table after the loop. `_html_draw_ir_commands` takes `widget_mode` separately from `widget_chrome_text`: the offset path is `widget_mode and not widget_chrome_text`.
- **Trap: a `{word:...}` inside a spec string literal is interpolation.** `"<style>body{margin:0}</style>"` fails with `variable margin not found`. Use a multi-declaration rule (`html,body{margin:0;padding:0;...}`), as the other rows do.
- **Proof recipe:** compare `simple_web_layout_render_html_software_pixels` (raster) with `simple_web_render_html_to_pixels_with_resolved_engine2d_backend(html, w, h, "cpu_simd")` over the whole frame, then the same call with `"vulkan"` under `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json`; `vulkan_readback_count()` delta proves the device ran.
- **Residue at the time (fixed in the next section):** widget page/node background suppression (549 px with an inline panel or body `background-color`) and the widget-image placeholder (raster paints it only outside widget mode: 384 px). Both need the per-node box-with-style command changed. Reach is fixture-only (production widget pages ship a `<style>`), so deleting legacy widget mode is the owner-call alternative.
- Specs, base -> head, same failing names otherwise: `simple_web_renderer_spec` 116/116 -> 118/118 (2 new rows, one #9850 assertion updated to the raster's offset text); `backend_vulkan_device_glass_blur_spec` 9/9 -> 10/10; `simple_web_engine2d_renderer_spec` 14/21 = 14/21; `browser_renderer_spec` 131/131 and 4/4; layout renderer coverage 36/39 = 36/39; paint primitives coverage 77/77 and 26/26; paint layout coverage 52/52; text byte codepoint residue 9/9; `widget_panel_text_divider_spec` 67/68 = 67/68.
- Legacy-page widget specs, base = head failing names (12 files): `theme_package` 2/3, `glass_css_backdrop_admission` 5/5, `glass_debug_interface` 24/24, `glass_css_output` 29/29, `dom_build_gpu_offload` 36/38, `simple_web_layout_child_index` 22/22, `simple_web_css_var_root_merge` 7/7, `simple_web_window_renderer` 14/28, `app/ui/html_render` 46/47, `web_wm_modern_shell` 3/5, `web_render_backend_api` 17/18, `03_system/gui/web_api` 13/16. Skipped (no style-free `widget-panel` page): `widget_draw_ir_theme`, office `html_render`. `check-cpu-hotloop-idiom.shs` is red on base with pre-existing violations; every new loop here is annotated.

## 2026-11-17 — Legacy widget box suppression and placeholder on Draw IR

- **Suppress the paint, keep the command.** In widget mode the html/body box and every `widget-*` / `icon-image` box still emit their Draw IR box command (id, geometry, owner node unchanged), but `_html_draw_ir_widget_suppressed_box` (`paint_layout.spl`) rewrites its paint props to the raster's `skip_widget_page_bg` / `skip_widget_node_bg`: fill color 0, `background-color` 0, gradient props cleared (left alone for a body with background layers), and for widget nodes border widths, `outline-width`, box shadow and typed shadow layers zeroed, with no styled border commands. Dropping the command would break id lookups and opacity owners.
- **Trap: `Style` is a `class`, so a reference type.** Mutating a "copy" of `styles[i]` mutates the shared style. Rewrite the emitted `DrawIrCommand` (a struct) instead.
- **Gated on `not widget_mode`, as the raster's `non_widget_mode`:** the widget-image placeholder, the checkbox/radio accent control and the select chevron.
- **Red -> green (raster vs `cpu_simd`, 40x64):** body bg 549 -> 0, panel bg 549 -> 0, panel border + shadow + outline 752 -> 0, placeholder 240 -> 0, checkbox 169 -> 0, select 16 -> 0. Vulkan (lavapipe) device pixel at the suppressed spot `0xFFFF0000` / `0xFF00FF00` / `0xFF2563EB` -> `0xFFF5F5F5`, device == `cpu_simd` on all three pages.
- **Residue, still divergent in widget mode (single-layer body radial fixed 2026-11-17, radial entry below):** a `body` radial background stack (1203 px, unchanged from base: the raster paints it, Draw IR paints the page base; `html` radial 1531 -> 0 and `body` linear 672 -> 0 were fixed by this change), URL background-layer commands on widget nodes (unprobed), inline `<svg>` 200, text `<input value>` 61, `overflow-y:scroll` scrollbar 300 px. The raster gates them on `non_widget_mode`; Draw IR does not. Recorded in `doc/08_tracking/bug/web_layout_cascade_selector_paint_chrome159_round4_divergences_2026-11-15.md`.
- Specs, base -> head, same failing names otherwise: `simple_web_renderer_spec` 118/118 -> 120/120; `backend_vulkan_device_glass_blur_spec` 10/10 -> 11/11; `simple_web_engine2d_renderer_spec` 14/21 = 14/21; `widget_panel_text_divider` 67/68, `html_render` 46/47, `simple_web_html_layout_renderer_coverage` 36/39, `web_render_backend_api` 17/18, `paint_layout_coverage_closure` 52/52, `widget_image_placeholder_draw_ir` 3/3, all unchanged. Legacy-page specs at head: `glass_css_backdrop_admission` 5/5, `glass_debug_interface` 24/24, `glass_css_output` 29/29, `simple_web_layout_child_index` 22/22, `simple_web_css_var_root_merge` 7/7, `browser_engine/browser_renderer` 4/4; base = head failing names for `dom_build_gpu_offload` 36/38, `simple_web_window_renderer` 14/28, `theme_package` 0 executed (string-brace parse error in the spec).

## 2026-11-17 — Legacy widget svg, input text, scrollbar and URL background on Draw IR

- **All gated on `widget_mode` in `_html_draw_ir_commands`, following the raster's `non_widget_mode`:** scrollbar lowering is never armed; the replaced-media emitter skips `svg` only (the raster paints video/audio in neither mode); static input value text is skipped but a live edit overlay target still paints (the raster has no overlay at all); the background-layer block (URL image commands and the border overlay) is skipped for a suppressed widget node and for html/body.
- **Trap: the background border overlay rebuilds its border from the raw style**, so a box-suppressed widget node with a URL background repainted its border (144 px) even after #9926.
- **Pixel proof with images:** `simple_web_render_html_to_pixels_with_resolved_engine2d_backend` takes no image resources, so URL backgrounds never lower there. Use `simple_web_layout_render_html_engine2d_result_with_images(html, w, h, "cpu_simd", [image]).pixels`.
- **Red -> green (raster vs `cpu_simd`, 40x64):** svg 200 -> 0, input `value='ABCD'` 69 -> 0, scrollbar 300 -> 0, widget-node URL background 144 -> 0. Vulkan (lavapipe) device `0xFFFF0000` / `0xFF000000` / `0xFF6B7280` (svg, input, thumb) and `0xFF0000FF` / `0xFFFF0000` (URL panel border 8,10, tile 11,10, via `..._engine2d_result_with_images(..., "vulkan", [tile])`) -> `0xFFF5F5F5`, device == `cpu_simd`.
- **Twin trap:** never assert raster == `cpu_simd` on a `<style>` twin; outside widget mode the raster paints the F5F5F5 panel fill and `cpu_simd` paints white (1144-2072 px, pre-existing). Assert `_count_color(cpu, X) > 0`.
- **Residue at the time, single-layer case fixed 2026-11-17 (radial entry below):** `body` radial stack in widget mode (1203 / 669 px). The raster's `fb_background_radial_stack_clip` (first stop only, linear alpha falloff by isqrt distance) has no Engine2D equivalent: `emu_draw_radial_gradient_stops` takes its centre/radius from the command box (`max(w,h)/2`), fills `d <= r` with opaque `draw_rect_filled` runs (no alpha blend) and ignores the box clip. Not attempted; needs a new primitive on `cpu_simd` + Vulkan or the owner call to delete legacy widget mode.
- Specs, base -> head, same failing names otherwise: `simple_web_renderer_spec` 120/120 -> 122/122; `backend_vulkan_device_glass_blur_spec` 11/11 -> 13/13; `simple_web_engine2d_renderer_spec` 14/21 = 14/21; `widget_panel_text_divider` 67/68, `paint_layout_coverage_closure` 52/52, `widget_image_placeholder_draw_ir` 3/3, `simple_web_html_layout_renderer_coverage` 36/39, `html_render` 46/47, `web_render_backend_api` 17/18, `scrollbar_wpt` 1/6, `simple_web_layout_child_index` 22/22, `dom_build_gpu_offload` 36/38, `web_wm_modern_shell` 3/5, all unchanged (same failing names at base and head).
- Trap (2026-11-17): the parsed-HTML layout root is `#document`, not `<html>`, so "the layout root is a BFC root" did not cover the real root element; `_is_root_element` checks the `html` tag. Pin root-element behaviour with a `BeDomNode.document()` > `html` tree, not a bare div root.
## 2026-11-17 — block-axis margins carry fractions (LayoutUnit-style cursor)

- **Fixed the css-paint vertical-drift class.** `Style.margin_t_milli` / `margin_b_milli` (milli-px, 0 = unset => whole-px margin) carry the UA h1-h6 em margins floored to Chrome's 1/64 px (21437 / 19906 / 18718 / 21265 / 22171 / 24968, all verified against Chrome including h4). `block_margin_milli(st, top, viewport_h)` in `..._layout_foundation.spl` is the ONE reader; the block loop in `..._layout_engine.spl` collapses on milli values and keeps `cy` = rounded y plus a residual `cy_frac` in [-500, 500). `LayoutResult.leading_margin_t` / `trailing_margin_b` are now milli-px. Box heights stay whole pixels.
- Spec: `test/01_unit/browser_engine/block_fractional_margin_chrome159_spec.spl` (Chrome y 20.906 / 189.53 / 238.25 / 274.25 pinned as painted rows 21 / 190 / 238 / 274; whole-px margins gave 239 / 275).
- **Trap — an author margin must clear the fraction.** `decl_apply` drops `margin_*_milli` whenever the cascade touched that side (`margin_t_pos >= 0` or a value change); a copy constructor that omits the two fields silently reverts a heading to whole px.
- **Trap — Chrome floors to 1/64 px, it does not round.** h2 `0.83em` of 24 is 19.90625, not 19.92: a +1 px offset on a 20-heading chain needs the floored value.
- **Not carried (known limits):** a container's own y is rounded before its children start (children restart `cy_frac` at 0), a container's height is whole px (residual dropped at its bottom), em/percent author margins still parse as whole px, flex/grid/contents/float-band margins stay whole px (flex main axis is another lane). h3 18.72px font size is still `i32`.

## 2026-11-17 — line-box strut uses the face's real ascent/descent (Chrome half-leading)

- **Rule (verified, Chrome 159, Liberation Serif 16px, standards mode):** ascent and descent are the face's own, each rounded to whole px (14 / 3; line gap 1, so `line-height: normal` = 18). Half-leading = `(line-height - (ascent + descent)) / 2`, FLOORED (true floor for negatives) and placed above; the remainder goes below. An inline-block 10x10 on the baseline sits at y = 7 / 5 / 4 / 4 / 10 / 15 / 0 / 1 for line-height 24 / 20 / 17 / normal / 30 / 40 / 10 / 12. A textarea or canvas that ends a line adds the strut descent below its bottom edge: 46 + 7 = 53 at line-height 24 (the old estimate gave 52).
- **Root cause:** `style_baseline_offset` (layout_foundation) was `font_size * 7 / 8` and `inline_line_strut_baseline_offset` split the leading on `font_size`, giving baseline 18 / descent 6 for a 24px line (Chrome 17 / 7). `inline_content_area_height` (9/8 em) disagreed with Chrome's 17 px content area too, which put a `<sub>` box 2 px high at 32px.
- **Fix:** `browser_face_ascent_descent_px` (font_renderer, same first-existing-candidate walk and measured-host scope as `browser_normal_line_height_px`) over `sfnt_line_metric_units_ascent_descent_px` (sfnt_kern). `style_face_ascent_descent` feeds `style_baseline_offset`, `inline_line_strut_baseline_offset` and the inline content area height/ascent. Off the measured host or without a face the old 7/8 estimate stays.
- Spec: `test/01_unit/browser_engine/line_strut_baseline_chrome159_spec.spl` (8 cases, red on 1add4219312 with y one px low). No other pinned spec moved; `sub_sup_baseline_shift` AC-5 stayed green only because the content-area ascent now follows the same real metrics.
- Catalog (1x, cpu_simd): forms-media 6.22 -> 4.73, animation 6.22 -> 4.67; every row lowered (overview 1.76, html 4.87, css-layout 4.09, css-paint 4.73); evidence 1.07 and tab-bar 0.48 unchanged. Per-page wall time unchanged (tab-bar 8955 -> 8965 ms, forms-media 84377 -> 85760 ms).
- **Known limit / open bug:** `<div>` with the default line-height holding `<span style="line-height:24px">x<inline-block></span>` lays out as two lines in Simple (h 48, inline-block y 34) where Chrome has one (h 24, y 7). Same on 1add4219312; independent of this fix.
- **Trap:** fractional line-heights (e.g. 1.5 x 13 = 19.5) are still whole px here; Chrome keeps the half-pixel.

## 2026-11-17 — CSS radial-gradient matches Chrome 159 (raster, cpu_simd, Vulkan)

- **One evaluator:** `radial_gradient_pixels` (`engine2d/backend_emu.spl`) — Q10 (1/1024 px) centre/radii, pixel-centre sampling, 1025-entry premultiplied-sRGB stop LUT (`_emu_gradient_color_at_q16`), seeded Newton isqrt per pixel, last stop past the end. Raster: `fb_radial_gradient_clip` (Engine2D `blend`); cpu_simd: `Engine2D.draw_radial_gradient_ellipse` -> `draw_image_blend`; Vulkan: the same host pixels composited on the device (`_draw_image_blend_native`, SRC_OVER). No new shader.
- **Geometry resolves once** in `paint_primitives.radial_gradient_geometry_q10` (circle/ellipse, closest/farthest side/corner — ellipse corner sizes are sqrt(2) x side, explicit px/%, `at <position>`) and travels to Draw IR as prop `background-gradient-radial-geometry` = `cx,cy,rx,ry,px,py,pw,ph` (Q10, relative to the command origin); `draw_ir_device_scale` scales it as an int CSV.
- **Canvas propagation:** a legacy-widget body radial paints the canvas, positioned on max(viewport, html box) (`canvas_background_extent`). Proven only for no-doctype (quirks) pages; standards-mode root positioning is untested.
- **Shorthand trap:** single-layer `background: radial-gradient(...)` used to flatten to its first stop (`decl_apply` over_layers==1 now types it radial).
- **Chrome measurement:** Chrome deviates <= 0.995/channel from the ideal model over 117,760 device px (5 frames, k=4), no dither; tolerance +-2. Oracle rows: `web_device_scale_spec` (A-E + raster), `simple_web_html_layout_renderer_coverage_spec` (two re-pinned rows), Vulkan row in `backend_vulkan_device_glass_blur_spec` (counter: `vulkan_image_reason_count(0)`; small/full-surface counts only move under timing).
- **Widget page E (40x64) cannot match Chrome at 40x64:** Simple's legacy widget layout gives the empty widget-panel section 56 px (Chrome 0), so Simple's html box is 72 px; pinned against Chrome at `--window-size=40,72` instead.
- **Residue (fixed 2026-11-17, gradient layer stacks entry below):** a body radial + linear stack (`radial(...), linear-gradient(...)`) was still unlowered on Draw IR, and neither lane painted the linear layer; raster vs cpu_simd 626 -> 1475 px because the raster's radial layer now covers the canvas (the older 669 figure came from a different fixture).
- **Perf regression (recorded in the bug file):** the 640x480 corpus page `10-radial-gradient.html` (530x300 radial box) costs ~1 s/render at base (flattened to its first stop: almost no work) vs ~6 s/render at head, interpreter only. Spec wall times are unchanged, but those fixtures are 40x64.
- **Probe trap:** importing `simple_web_html_layout_renderer` alone demotes a probe from the seed JIT to the interpreter (`cannot infer field type while lowering interpolate: struct 'ANY' field 'b'`), at base too; a probe without that import runs JIT. So every web-render probe timing is interpreter timing.

## 2026-11-17 — Multi-layer gradient backgrounds match Chrome 159 (raster, cpu_simd, Vulkan)

- **Path:** a raw gradient-only background list (`gradient_layer_list`, foundation: every image layer a plain `linear-gradient(`/`radial-gradient(` with >= 2 stops, optional trailing colour layer) -> `background_gradient_layers` (paint_primitives: per-layer geometry against the background positioning area; radial `radial_gradient_geometry_q10`, linear `linear_gradient_line_q10` = gradient line start/end in Q10, |w sin| + |h cos| long) -> raster `fb_gradient_layers_clip` / Draw IR props `background-gradient-layer-geometry` (paint rect + 4 lengths per layer, device-scaled; radial [2],[3] are radii) + `background-gradient-layer-stops` (`R|L:<colours>:<permille>;...`, unscaled) -> `draw_ir_adv` -> `Engine2D.draw_radial_gradient_ellipse` / `draw_linear_gradient_line` -> `draw_image_blend` (Vulkan: device SRC_OVER). Layers paint last-to-first over the box colour.
- **One linear evaluator for stacks:** `linear_gradient_pixels` (`backend_emu`), the radial twin (shared `_emu_gradient_stop_lut`, 1025 entries). Typed single linear layers keep their existing paths (raster dithered 180deg row painter + `fb_linear_gradient_general_clip`, Draw IR `emu_draw_linear_gradient_stops`): measured already +-1 of Chrome at k=4, so not migrated.
- **Traps:** (1) a single linear ending in `transparent` is NOT typed (`_background_is_exact_typed_linear_layer` rejects a zero stop, and `from/to != 0` gates every typed-linear site); it now takes the gradient-list path. (2) The `background:` raw branch used `parse_color_alpha(whole list)` = the first gradient stop as `bg`; only the trailing colour layer counts now. (3) `fb_background_radial_stack_clip` stays radial-only (the closure spec pins "non-radial layers are ignored"); the widget body canvas path calls `fb_gradient_layers_clip` when the list is gradient-only. (4) Python late binding in scratch model scripts: bind loop variables as lambda defaults or the "ideal model" lies.
- **Chrome measurement:** Chrome vs ideal model: <= 0.98 per channel on one linear layer, <= 1.88 on a two-layer stack (each layer dithered). Simple vs model: <= 0.53 / <= 1.85; most of the stack error is Engine2D `blend` truncating (open, recorded in the bug file). Full-frame Simple vs Chrome: single layers +-1, stacks max 3 at 4-7 of 20,480 px; oracle rows sample at +-2 (`web_device_scale_spec` gradient-stack describe, Vulkan row in `backend_vulkan_device_glass_blur_spec`).
- **Typed linear over a colour:** `draw_ir_adv`'s typed stops branch now fills `command.color` before `draw_gradient_rect_stops` (it painted a translucent linear over the page, not the box colour). **Gate:** gradient lists with a non-default `background-size` or a px `background-position` stay fail-closed (colour only); size/tiling per layer is still unimplemented.
- **Widget page sample points** must avoid Simple's widget chrome (panel frame plus two inner boxes at rows 128-184 / 200-256, x 20-116 / 20-136 at k=4): (100,160) lands on one.
- **Perf (hybrid JIT/interpreter mode, not #9960's interpreter numbers):** 640x480 stack page 12.2 s / 2.0 GB (base, wrong) -> 8.3 s / 1.4 GB (head) for 1 raster + 2 cpu_simd renders; `10-radial-gradient.html` unchanged within noise. Numbers in the bug file.

## 2026-11-17 — dpr4 residual per-pixel cost: shadow and PPM encode

- **Fixed (pixels byte-identical, PPM sha256 equal on tab-bar, evidence, forms-media at dpr4):** `emu_draw_shadow_rect` (`backend_emu_adv.spl`) skips zero-coverage rows/columns, fills the constant interior with one formula + one `write_span` when the destination segment is uniform, and reads only the surface-clipped region; `encode_ppm_p6` (`common/image/ppm_decode.spl`) writes flat rows and 64-pixel blocks as one `write_span` of a doubling-built RGB pattern. Shadow 31.2 s -> 5.7 s (evidence-size), PPM 21.0 s -> 3.4 s (3600x3040). Whole pages: tab-bar 96 -> 81 s, evidence 258 -> 212 s, forms-media 306 -> 284 s, RSS within +-1.1 %.
- **Trap:** in the interpreter a read method (`slice`, `min`, `max`) interleaved with `write_span` on the same array re-decodes its whole backing store (11-13 ms at 3.66 M px). Keep one read-only `src` and one write-only `outp`. Bug record: `doc/08_tracking/bug/interpreter_array_read_after_write_redecodes_backing_2026-11-17.md`.
- **Trap:** the shadow was NOT the dominant cost of the box command (about 30 s of 113 s); do not extrapolate a per-phase share from a command total.
- **Open / not investigated:** glyph raster on an atlas miss (item 2) and full-frame fills (item 4); remaining page time not attributed per phase. Details: `doc/08_tracking/bug/web_render_dpr4_residual_per_pixel_cost_2026-11-16.md`.

## 2026-11-17 — selectors round 4 (adopted from abandoned `28dff1927c4`)

- **Two compound fixes now coexist.** Upstream `_compound_base_tokens` reads
  the base (tag/#id/.class) in any order. `_canonical_compound` (run on every
  part `selector_group_parts` returns) also moves a pseudo-class written
  BEFORE a class or id behind it, so `:is(p, div).k` and
  `div:first-of-type.k` match. Both matcher paths consume
  `selector_group_parts`, so one fix reaches the text and the pre-parsed path.
- **Of-type codes:** upstream's `PSEUDO_FIRST_OF_TYPE` (16), `PSEUDO_LAST_OF_TYPE`
  (17) and `PSEUDO_ONLY_OF_TYPE` (18) won the merge; the abandoned lane's
  "map first-of-type to nth-of-type(1)" variant was dropped. A new
  pseudo-class must still be added to both `simple_match`/`_pseudo_ctx_matches`
  and `_pseudo_code_for`/`_pseudo_ctx_matches_parsed`, or
  `web_selector_parsed_equivalence_spec` diverges.
- **Invalid vs unsatisfied.** `_pseudo_code_for` returns -1 for both an unknown
  name and a valid-but-static-false one (`:hover`). Only an unknown name drops
  the whole rule: `selector_list_has_unknown_pseudo`, called once per rule in
  `_extract_css_vw_with_rule_limit` (the only rule-admission site). It
  recurses into `:not()`, `:has()` and the `of S` of `:nth-child()` /
  `:nth-last-child()`, NOT into `:is()`/`:where()` (forgiving in Chrome), and
  checks `::` names against `CSS_KNOWN_PSEUDO_ELEMENTS` (`::-webkit-*` always
  accepted).
- **Validate the name tables against Chrome, not memory.** A `<style>` probe
  (`st.sheet.cssRules.length` after `div:NAME{}`) found `:first`, `:left`,
  `:right` and `:blank` rejected in style rules (@page-only) and
  `:active-view-transition` missing. A name missing from a table drops valid
  rules on real pages, so add before you remove.
- **Still permissive (keeps a rule Chrome drops):** any `:-webkit-*`
  pseudo-class (Chrome rejects `:-webkit-frob`), a pseudo-class after a
  pseudo-element (`::before:hover` is invalid, `::part(x):hover` valid), a
  pseudo-element inside `:not()`, and `:nth-of-type(1 of p)` (`of S` is
  nth-child only).
- **Gates at the fix (2026-11-17, Chrome 159.0.8154.6, seed `cargo-target-webrender-vk`):**
  matrix 979 cells, 88 mismatching (base 88, no change). Selector structural spec
  base 62/71 -> head 71/71. 25 nearby specs, no new failing names.
  `simple_web_html_layout_renderer_module_split_spec` "keeps every parser input
  below 128 KiB" was already red at base (`..._core_selectors.spl` 138,390 B),
  and this change grows the file to 147,903 B. Split the file before adding more.
## 2026-11-17 — slight vertical hinting (Chrome FreeType autohinter, y only)

Glyph residual was ~75% of css-paint. Classified on a probe page (16 px sans, 16 px serif, 13 px sans, black on white, 3 lines, 2,791 mismatching px at tolerance 8 before the fix, heuristic split; scripts were scratch .spl, not committed):

| rank | class | px (base) | share | status |
|------|-------|-----------|-------|--------|
| 1 | vertical metrics: no y hinting (cap 11 rows vs Chrome 12, x-height 8 vs 9, baseline/bottom rows blurred) | 772 | 27.7% of the mismatch | FIXED (`sfnt_glyf.spl`) |
| 2 | horizontal-stem edge snapping (H crossbar, e bar: Chrome puts the TOP edge on a row boundary) | ~1,025 (delta 17-64 after fix) | ~37% | open |
| 3 | low-amplitude coverage / FIR / gamma (delta 9-16; ink 2.9% under Chrome after fix, 8% before) | ~876 | ~31% | open |
| 4 | advance / kerning (per-word ink centroid within +-0.23 px, one word -0.65 px) | <1% | - | none at 16 px |

- **Measured Chrome behaviour.** Liberation Sans 16 px: H is 12 rows (unhinted 11.0), x is 9 rows (8.45), g descender and l ascender land on the same rows as ours after the fix. This is FreeType's latin autohinter in light mode: (1) the y scale is fitted so the x-height is a whole pixel, `fitted = floor(scaled + 40/64)`, with `52/64` for 6..14 ppem (`increase-x-height` defaults to 14); (2) each blue zone (baseline, x-height, cap height, ascender, descender) is snapped to a whole row and the overshoot collapses onto it unless it is >= 1/2 px.
- **Code.** `_lcd_hint_knots` builds piecewise-linear font-y to pixel-y knots from the font's own `x o H O l p g` outlines (cached per font + size in `_lcd_hint_cache`); `sfnt_render_glyph_lcd` warps the outline y with `_hint_commands` and now anchors the raster to the BASELINE (`bearing_y` = floor of the hinted bottom). Before, the bitmap was anchored to the ink bottom and `bearing_y` was `round(min y)`, so a glyph's rows could sit up to half a row off. Unhinted fonts (no `x o H`) keep the old path.
- **Trap — a `[a, b]` literal on the line after a `match` arm parses as an index of the arm.** Bind it (`val extent: [f64] = [...]`) first.
- **Trap — ink count is not a closeness metric.** `web_device_scale_spec` 1x ink went 190 to 186 while Chrome measures 146 on that exact crop (the "199" in the LCD section was a different crop); per-pixel mismatch against Chrome went 114 to 77 of 960. Compare per pixel.
- **Not done.** The grayscale raster (above 48 device px, `sfnt_render_glyph_into`) is not hinted: the 4x `Hg` frame is unchanged (827 of 15,360 px mismatching Chrome). Horizontal-stem edge snapping (rank 2) needs edge detection and stem placement, not a blue-zone warp.
- **Open — 8 px text.** `simple_web_renderer_spec` "uses explicit line-height for wrapped text layout" pins the darkest ink px (`0xFF352A44` x 2). Hinting now gives the 8 px caps Chrome's 6 rows, but that pin is a pen-phase statistic (Chrome's L stem sits about half a pixel right of ours): text-box mismatch 711 to 709 px, sum of abs delta +1.3%, darkest px `0x283151` (Chrome `0x483E5F` x 1). Not strictly closer, so not re-pinned; the spec stays red until the 8 px pen phase is fixed.
- Spec: `test/01_unit/browser_engine/glyph_shape_vertical_hint_chrome159_spec.spl`. Bug record: `doc/08_tracking/bug/web_render_css_paint_residual_2026-11-17.md`.

## 2026-11-17 — CSS opacity groups (saveLayer) match Chrome 159

- **Chrome's rule (fitted, not guessed).** A box with `opacity < 1` and two or more painted items rasterises its subtree into a transparent premultiplied 8-bit layer (children use the solid rule), then restores it with paint alpha `A = round(opacity*255)` through SkBlendARGB32: `sc = A+1`, `p = 0xFFFF - La*sc`, `ds = (p + (p>>8)) >> 8`, `out = (L*sc + D*ds) >> 8` on every channel. Fit: 601884/604800 (single level) and 602574/604800 (nested, 2-decimal opacities) channels; a no-group control page is 604800/604800. Rejected: NEON lowp `div255r`, `S32A_Blend`, 2-term truncation, float.
- **Tile seams are Chrome's, not the rule's.** Every miss sits in a few device columns just left of x = 256*k (k >= 2), +-1 (rarely 2), only on group pages, and the runs stay at the same device x when the content moves 16 px. Pin cells inside one 256-device-px tile; a full-frame row across a seam asserts max deviation <= 2 (`opacity_group_chrome159_spec`).
- **Code.** The math lives only in `engine2d/css_opacity_group.spl` (alpha mapping, pixel restore, region restore, surface-id prefix `html-opacity-group-`). `engine2d_composite_region_milli` is untouched (its 930 -> 117 oracle is Simple-internal).
  - Draw IR: `_simple_web_opacity_root_bounds` gives each opacity root a surface rect = union of its commands clipped to the viewport. A root with an untranslatable command (glyph runs, points, fractional/affine geometry, paint transforms, CSS background images) or a member with box-shadow/outline (halo outside the command rect) keeps a viewport surface — but only a SINGLE such root is admitted; on a page with two or more roots one such root turns surfaces off for the whole page (base behaviour: flat, no opacity). >= 2 painted commands name the surface as a group; `draw_ir_adv` routes it to `Engine2D.draw_ir_composite_readback_css_group` (region readback + .spl restore + opaque `draw_image`, all backends, so Vulkan == cpu_simd). A box's border and outline ride its background command but count as items of their own (once per owner), matching the raster. One painted item keeps the old single-item surface.
  - Vulkan: `Engine2D.draw_ir_composite_device_css_group` restores the layer straight from the shared offscreen's device buffer with `shaders/css_group_restore.comp` (integer twin of `css_opacity_group_composite_pixel`; generated `backend_vulkan_css_group_restore_spirv.spl`, pinned by `scripts/check/check-css-group-restore-spirv-pinned.shs`, regenerated by `scripts/tool/gen-css-group-restore-spirv.shs`). It is submitted on its own after a flush, because the layer buffer belongs to another backend and must not enter the pending-source release list. Clip, mask or a host fallback on either side declines to the readback restore. Counter: `vulkan_device_css_group_restore_count`.
- **Trap: Vulkan region readback is a whole-frame read.** `read_pixels_region` on Vulkan inherits the RenderBackend default (full-frame read + host crop) and, without `SIMPLE_VK_READBACK=native`, the read is an interpreted per-pixel unpack (~5 us/px). The first group restore spent 713 ms of ~900 ms per 140x60 group there (600x200 frame); never read the destination back for a per-element composite on Vulkan.
  - Raster: `paint()` is now a front end over `_paint_passes`. Admitted groups are painted with their members hidden, then each group is painted alone into a bounded layer (coordinates shifted, root opacity forced to 100) and restored after the passes — Chrome's order for a z-auto stacking context relative to in-flow content. Ops are counted like Chrome (bg + border on one box = 2 ops = a group: Chrome paints `ff7e7e`, not the folded `ff7f7f`). Not admitted: nested groups, iframes, widget pages, html/body roots, a group overlapped by a positioned box that paints above it (later in tree order or z > 0), and any member the transparent layer cannot hold exactly (shadow, gradient, image, form control, translucent colour, text without an opaque root background) — the raster blenders treat a transparent destination as opaque black.
- **Trap: multi-root pages lost their opacity entirely.** Before this, two or more opacity roots that were not `overflow:hidden` and equal-sized failed admission and painted FLAT at full opacity on cpu_simd/Vulkan; the raster painted group children unfaded. A group page at base is wrong by tens of levels, not by one.
- **Follow-ups.** Multi-root Draw IR pages where any root holds text, a shadow or an outline still paint flat on cpu_simd/Vulkan (needs per-root text translation and halo padding). Nested groups (the Draw IR producer still refuses `parent_root >= 0`). Translucent children on the raster: a translucent child over a transparent layer pixel gets alpha 255 (measured `166975` vs Chrome `1e7b9d`); cpu_simd/Vulkan match Chrome on that probe. Vulkan cost is now ~19 ms per 140x60 group (offscreen create 1 ms, render 15 ms, device restore 2-5 ms).

## 2026-11-17 — Chrome 159 source-over rule measured; blend fix BLOCKED on native kernels (red rows only)

- **Two Skia rules, both fitted exactly** (arm64 software raster; `--disable-gpu` output is byte-identical):
  - Solid colour fill (rgba background, `opacity` folded into the paint alpha, alpha `= round(css * 255)`): `round(s*a/255) + ((d*(256-a)) >> 8)` (SkPMSrcOver). Fits 6096/6096 single-layer, 3072/3072 two-layer, 1059/1059 `opacity`, 594/594 decimal-alpha channels, plus 2032 + 2032 channels with the source and destination terms isolated.
  - Shader/image composite (gradient layers, `<img>`): `round(s*a/255) + div255r(d*(255-a))`, where `div255r(v) = (v + 128 + ((v + 128) >> 8)) >> 8` (raster pipeline lowp, NEON exact divide). Fits 12288/12288 channels of a translucent pixelated PNG over an opaque one. The solid rule fits only 8659 of those, so do not use one function for both.
- **Base lanes:**
  - cpu_simd and Vulkan truncate (`(s*a + d*(255-a)) / 255`).
  - The raster's `composite_over_base` rounds the ideal; its percent `blend_opacity` gives `#ff8080` where Chrome gives `#ff7f7f`.
- **Blocker, partial (measured with temporary `color.spl` edits, reverted):**
  - **Solid fills are blocked.** With the solid rule in `blend`, the six cells did not move on cpu_simd or Vulkan (`4c 05 ff8080 b2`). On a NEON/AVX2 host the unclipped translucent rect spans run in the seed's Rust kernel (`rt_engine2d_simd_blend_const_span_u32` -> `blend_pixel`, `runtime/src/value/engine2d_simd_ops.rs`; interpreter twin `engine2d_blend_pixel_u32`). Vulkan reads back the same truncated value, so Vulkan solid fills are composited by the CPU rule, not by lavapipe float blending (which would give `06` / `4d`). The raster's `opacity` spans use `rt_engine2d_blend_const_span_pct_u32` (Rust).
  - **Gradient-layer composites are not blocked.** They do reach `.spl` `blend` on cpu_simd: 4471 / 4798 of 20,480 px moved on S1 / S2, with deviations identical to the raster.
  - **Why `blend` cannot simply change:** `blend` is also the clipped solid-fill path (`sw_set_pixel_blend`). Changing it alone splits clipped from unclipped solid fills, and the raster from cpu_simd (`web_device_scale_spec` pins `gstack_mismatches == 0`).
  - **Perf of routing:** sending the spans to the `.spl` scalar loop costs about 62 µs/px in the interpreter (5089 ms vs 0-1 ms native for 81,920 px). The Rust kernels plus a seed redeploy are the owner's call.
- **`opacity` group (saveLayer, >1 child): superseded by the opacity-group entry above (#9986, SkBlendARGB32 restore).** Original note: No two-term 8-bit candidate fits: best `round(S*a/255) + d*(255-a)//255` at 1060/1524, float ideal 750/1524. The bias is -0.5..-1 vs ideal. A single solid child folds into the solid rule (1059/1059).
- **Feasibility (temporary `.spl` experiment on the raster, reverted):** with the shader rule, full-frame max deviation on the #9970 stacks S1/S2 drops from 3 (4 / 7 px) to 2 (0 px). With the solid rule it is still 3 (1 / 2 px).
- **Red rows:** `test/01_unit/browser_engine/translucent_blend_chrome159_spec.spl` (0/5 at base).
  - Six cells on cpu_simd, raster and Vulkan.
  - Full-frame S1/S2 at k=4 against the Chrome PNGs in `test/fixtures/browser_engine/blend_chrome159/`.

## 2026-11-17 — Chrome 159 source-over implemented on every lane (supersedes "BLOCKED" above)

- **Rules (one each, shared):** `color.spl` `_blend_rule(src, dst, solid)`; `blend` = image rule, `blend_solid` = solid rule. Twins: C `engine2d_blend_u32(s, d, solid)` (`runtime_simd_dispatch.c`), Rust `blend_pixel(s, d, solid)` (`engine2d_simd_ops.rs`) and `engine2d_blend_pixel_u32` (`interpreter_extern/simd.rs`), oracle `oracle_src_over_chrome`, GLSL blit (`_glsl_blit`, mode 1 image, new mode 2 solid), MSL `blend_rule` (`blend_src_over` = solid, `blend_src_over_image`). Translucent dst: straight src-over with every division rounded (`dw = (da*(255-sa)+127)/255`, channels `+oa/2`).
- **Which rule where:** solid fills (rect, circle, rounded rect, triangle, gradient-rect rows via `draw_rect_filled`, `buf_set_pixel_blend`, const spans, percent `opacity`) = solid; image/layer composites (`draw_image_blend`, blend_row/blend_span, gradient-layer stacks, raster typed-linear gradient rows) = image. Opacity scale rounds: `ea = (a*milli + 500)/1000`, percent `a = (pct*255 + 50)/100` (Chrome `round(css*255)`; `ff7f7f` needs alpha 128).
- **Kept on the old truncating rule, deliberately:** the coverage MASK (`oracle_mask_src_over`, C `rt_engine2d_blend_mask_span_u32`, `simd_isa_mask_src_over`) — no Chrome grayscale-coverage measurement exists (the LCD lane only measured LCD16), so text pixels stay as they were; the glass material (`_glass_blend_over`, MSL `glass_blend_over`, `glass_material.comp`) — WM surface with no Chrome equivalent.
- **SIMD kept:** NEON/SSE2/AVX2/RVV bodies compute both rules in 16-bit lanes (exact: products <= 65280), select sa==255/0 lanes, and send translucent-dst lanes to the scalar rule (`engine2d_blend_lanes`). NEON proof: `engine2d_simd_span_test.c` sweeps 3,559,424 px per kernel (every sa x 4096 random dst, 1/8 translucent) against the scalar rule; two hand mutations of the NEON body make it fail (rc 12/14). x86/RVV are compile-only on this host (`-fsyntax-only` + `-O2` cross objects).
- **Trap — percent quantisation:** the raster typed-linear row painter passed the gradient stop alpha as a percent (16 -> 6% -> 15), which the old percent formula happened to absorb; with the solid rule it moved the Aetheric pin off Chrome's `#575758`. Gradient rows now pass `image_alpha255` to `fb_rounded_rect_row_span_opacity_clip` and composite with the image rule (`fb_blend_image_row`, native blend_span on a row copy).
- **With the opacity group (#9986):** the restore keeps its own SkBlendARGB32 math (`css_opacity_group.spl`, no double rounding: alpha8 = round(milli*255/1000) once); layer children paint through Engine2D/raster fills, i.e. the solid rule implemented here. A single painted item takes the fold path (`engine2d_composite_region_milli`: rounded alpha + image rule) and gives Chrome's `#ff7f7f`.
- **Trap — seed carries the rule:** interpreter runs take blend_const_span/blend_span/pct from the SEED's Rust kernels, so head lib on the old seed still truncates those spans. A rebuilt seed (`~/.cache/cargo-target-webrender-blend`) also rejects importing private `sfnt_render_glyph_lcd` / `gradient_corner_dir_q16` (23 failing rows, 21 of them new against the reference seed; identical with base lib + rebuilt seed, so visibility debt, not blend).
- **Perf (NEON, aarch64 host, `-O2` C bench, 4096 px x 2000 reps, best of 5, ns/px base -> head):** blend_into 5.06 -> 0.77, boxed span 2.98 -> 0.88, boxed const 3.64 -> 0.68, pct 0.90 -> 0.68 (base scalar bodies are slower than the vector rule).
- **Sweep (48 blend-adjacent specs, failing-name diff vs base lib on the reference seed `cargo-target-webrender-vk`):** head lib + rebuilt seed: 0 new blend failures, 21 new names all the private-import rejection above, 6 fixed (5 red rows + embedded `opacity_milli=500`). Head lib + REFERENCE seed: 41 new names, every one a native-span vs `.spl`-rule parity row (the old seed's Rust spans still truncate) — so this change needs the seed redeploy to land green.
