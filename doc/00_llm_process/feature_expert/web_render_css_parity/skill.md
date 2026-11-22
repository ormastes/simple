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
- 2026-11-17 `layout.spl` `_layout_block_node` fifth pass (margin collapse round 2): empty blocks self-collapse (`_self_collapses`: no own BFC, no vertical padding/border, height auto or explicit 0, min-height 0, every in-flow child self-collapsing); such a child is placed at `cursor + value(prev ∪ its top set)`, adds no height, and joins its whole set into the running set (or into the parent's top set when it leads a top-through parent). `_top_margin_set`/`_bottom_margin_set` walk past self-collapsing children. New `StyleProps.height_zero` (explicit zero length; NOT `css_declared("height")`, which is also true for `auto`/`%`) and `StyleProps.min_height`. Trap: Chrome blocks the bottom parent/child collapse only when min-height RAISES the height (min-height 5px under 10px content still collapses), so the decision is made at layout time and handed up in `BeLayoutBox.after_margin_pos/neg` instead of the static set. Floats/abs boxes and whitespace-only text are skipped for collapsing (float/abs at `cursor + prev + own margin-top`, no cursor advance; a BFC-root box still contains its floats); grid items never collapse (`collapse = not items_bfc`). Spec rows `mc-*`: 16 red -> green, 5 guards. Open: per-side borders (not parsed), clearance, float avoidance.
- 2026-11-17 `browser_engine` per-side borders (`layout.spl` `_layout_block_node`, `layout_core.spl`, `BeLayoutBox`): `StyleProps` now stores specified `border_<side>_width` (initial `medium` = 3px) and `border_<side>_style` (initial `none`); layout reads the USED width through `border_top()`/`border_right()`/`border_bottom()`/`border_left()` (0 for none/hidden). `border_width`/`border_style` are gone; fixtures use `style.set_border_all(w, "solid")`. **Trap: resolve the used width at read time, never at parse time** — `border-width:5px` then `border-style:solid` must give 5, `border-style:solid` alone 3, `border-style:solid;border:5px` 0 (the shorthand resets the omitted style), and parse-time zeroing gets at least one order wrong. **Trap: `border-width` with no style is 0 in Chrome**, so a fixture that only sets `border-width` measures nothing; two older fixtures (`layout_box_content_contract_spec`, `ui.chromium/css_spec`) gained `border-style:solid`. Only top/bottom borders stop self-collapse (an empty block with just `border-left` still collapses, Chrome). Paint keeps one `stroke_rect` for a uniform border, else one `fill_rect` per side. Rows `bw-*` (Chrome 159): 18 red -> green, 2 guards. Open: per-side border colours / `currentcolor`, fractional-width device-pixel snapping. Bug record: round-4 file, section "Per-side borders on `_layout_block_node`".
- 2026-11-17 `layout.spl` `_layout_block_node` floats and `clear` (sixth pass): a `BlockFloats` context (margin-box rects in page coordinates) is created by every BFC root (`own_bfc or _establishes_bfc`) and shared BY REFERENCE down non-BFC boxes, so `clear` sees floats from earlier sibling subtrees (cl-10) and a BFC root's height takes the max float bottom of its own context (a non-BFC parent of a float stays h0). Placement (`_float_place`): outer top = max(static position, earlier float tops, own clearance), then down past float bottoms until the margin box fits beside the floats meeting `[y, y+h)`; right floats take `right edge - outer width`. Clearance: border edge = relevant float bottom when the hypothetical edge (margins collapsed as if `clear:none`) is above it; the cleared box then stops the collapse and its own margin is dropped (negative too). BFC root (`overflow`/`flow-root`) beside floats: border x = max(left + margin-left, float edge) — its margin may overlap the float — and an explicit width that does not fit drops to the next float bottom. **Trap — clearance across a parent boundary is decided BEFORE layout** (`_top_margin_set` runs on the DOM): Chrome stops a first child's margin from collapsing through its parent when it clears a float that precedes it in that parent (even a 5px float with a 20px margin: child y=5, parent y=0) or when the collapsed hypothetical edge is above an earlier float; so `_top_margin_set` takes the float context and a base y. **Trap — clearfix:** an empty `clear:both` after a float is not self-collapsing, and neither is its parent (`_self_collapses` checks for a sibling float), otherwise the parent is skipped as empty and the next sibling overlaps it. **Trap — a dropped BFC root has no float at its new y**, so keep the new y even when `_bfc_place` reports "no float here" (width -1). **Trap — a `display:none` float is no float:** every "preceding float" scan must check `_generates_box` first (cl-h1, cl-h3). **Trap — a box that took height in layout is not empty** even when the static `_self_collapses` says so (its empty `clear:both` child cleared a float OUTSIDE it, cl-h2). Spec `layout_block_float_clear_chrome159_spec.spl`: 27 red -> green, 13 guards (base 13/40, head 40/40). Open: float shrink-to-fit, BFC fit tested at the top edge only, line-box shortening (no inline layout on this path), floats in flex/grid, layout root margins.

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
- **Tables travel in the params buffer, not a 4th binding.** The seed fixes the pipeline layout at bindings 0..2 (`interpreter_extern/gpu.rs` ~5054). The glyph record stays 7 words (Metal parity, `VULKAN_FONT_PACKED_MAX_BYTES == 114720`). Header word 7 bit 31 marks an opt-in trailer after the glyph records: `G` words (low 16 bits = table index, 0xFFFF = no LCD; high 16 bits = chain length, see "Chains" below) then one 768-word s32 table per distinct LCD text colour (cap 32; more is refused, not drawn gray). Tables come from `engine2d_lcd_s32_tables` (`helpers/lcd_s32_tables.spl`, moved out of `engine.spl`, not duplicated). The pooled params buffers are `VULKAN_FONT_PACKED_POOL_BYTES` (max + trailer).
- **Trap: the 5x7 bitmap atlas has rgb = 0**, which the LCD-cell test would read as "LCD cell, zero coverage" and blank the text. The packer skips LCD for `VULKAN_BITMAP_FONT_CONFIG_IDENTITY` batches.
- **Trap: clip trimming hides surface overhang.** Draw IR clips each text box, so `vulkan_bitmap_text_clip_quads` bakes the clip into the quad and the kernel only sees the on-surface part. The CPU reads the UNTRIMMED quad back (off-surface reads as 0, not opaque) and paints an overhanging quad (a glyph at x=0 or flush right, because LCD padding reaches 1 px out) gray. `vulkan_font_lcd_veto_keys` records those trimmed quads on `VulkanBackend.font_lcd_veto_keys` and the packer draws them gray. Without it a page with margin:0 text differs on the first/last glyph.
- **`runtime-glsl` keeps the legacy layout.** The packer only emits the trailer and the X = 1 grid when `pipeline.artifact_mode == "precompiled-spirv"`; the common gray GLSL has no stride loop and would draw 64 pixels per glyph.
- **Chains: an overlapping LCD batch is ONE dispatch (2026-11-19).** LCD quads carry 1 px of padding, so the glyphs of a word overlap. `vulkan_font_partition_quads` (bucket = 1 + highest earlier overlapping bucket) then needed one dispatch per glyph of the longest word, and each sub-batch re-ran the whole composite (validate, identity, 768-word table pack). Now `composite_font_batch` sorts each connected group of overlapping quads ("chain", `vulkan_font_chain_ids/_order/_lens`) into consecutive records in painter order, and the kernel workgroup of a chain's first quad blends the whole chain, quad after quad, with `memoryBarrierBuffer(); barrier();` between quads; the other members' workgroups return at once. Chains share no pixel, so no race. Taken only when the batch overlaps, the kernel is `precompiled-spirv`, and `vulkan_font_lcd_color_count` is 1..32 (the batch WILL carry the trailer). Gray batches, `runtime-glsl`, and more than 32 colours keep the split.
  - Measured (lavapipe, blend seed, typed atlas upload): 900x760 three-family text page 456 -> 60 font dispatches, `font_packed_params` 2556 -> 635 ms, `font_composite` 6195 -> 5405 ms, wall 25.6 -> 24.2 s (cpu_simd 29.9 s); 12 one-face pages (sans/serif/mono x 4 styles, 8..64 px) 28..62 -> 10..12 dispatches each.
  - Byte equality: cpu_simd == Vulkan head == Vulkan base on all 12 pages and the text page at 1x. At device scale 4 Vulkan head == Vulkan base on all 12, but cpu_simd != Vulkan on BASE too (not from this change, not investigated).
  - Spec: `vulkan_font_lcd_packed_params_spec` ("packed Vulkan font LCD chains", host) and `lcd_subpixel_text_chrome159_spec` AC-8 (device, words).
  - **Trap: a kernel edit needs the blob regenerated**, never hand-edited: `glslangValidator -V`, `scripts/tool/spirv-to-spl-words.shs <spv> 8`, split the body into the head / tail halves of `backend_vulkan_font_spirv.spl`, update both header sha lines and `FONT_ATLAS_COMPOSITE_VULKAN_SPIRV_SHA256`, then `sh scripts/check/check-font-atlas-batch-spirv-pinned.shs`.
  - **Trap: wall time on Vulkan is the atlas upload, not the dispatch count.** With the default byte upload the same text page takes 308 s (base 324 s), 287 s of it in 60 full `[u32] -> [u8]` atlas repacks; `SIMPLE_VK_FONT_UPLOAD=u32` gives the 24 s above with equal bytes. See `doc/08_tracking/bug/vulkan_font_atlas_full_repack_interleaved_faces_2026-11-19.md`.
- **Cost (2026-11-17, before chains):** LCD on Vulkan was about 60 % slower steady (cold several times) than gray on a 900x760 text page; gray is unchanged within ~5 %. See the bug record, open items 5-6, for numbers and an unexplained RSS drop.
- **CUDA / OpenCL / Metal LCD remain open (2026-11-17, gpulcd lane: investigated, nothing implemented).** `_lcd_text_active` (`engine.spl` ~2751) admits only cpu/cpu_simd/software/vulkan. No device-run verification is possible on the sanctioned seed, so no red-to-green pixel spec exists, and none was written (a spec asserting only `resolved_backend` equality would be green on base, because the `cuda`/`opencl` requests resolve to `software`, which already paints LCD on its CPU mirror):
  - **OpenCL.** `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:2836-2858` stubs `rt_opencl_create_context`, `rt_opencl_create_queue`, `rt_opencl_create_program`, `rt_opencl_build_program` (return 0 / false), so `OpenClBackend.init` fails with `opencl-program-build-failed` (`opencl_session.spl:167`). The kernel source is not at fault: a scratch C harness over `libOpenCL.so.1` built the generated source (`opencl_2d_generated_source`) with `clBuildProgram` = 0 on the NVIDIA ICD. Existing specs `backend_opencl_facade_spec` (6) and `backend_opencl_text_fallback_spec` (2) pass (they exercise the CPU mirror).
  - **CUDA.** `rt_cuda_init()` returns 3 and `rt_cuda_device_count()` 0 through the seed (`gpu.rs:1311` non-`cuda`-feature path via `get_cuda_dl`, `libcuda.so.1`), while a native `cuInit(0)` on the same host returns 0 with 1 device (GB10). `backend_cuda.spl:313` therefore reports `cuda_runtime` unavailable. Pre-existing on base in `backend_cuda_renderbackend_spec`: 2 of 31 fail ("routes both CUDA image blend interfaces through the native kernel", "propagates CUDA font completion state to facade readback"); `backend_cuda_processing_spec` (7) and `backend_cuda_font_launch_args_spec` (1) pass.
  - **No CPU-executable kernel form exists** (`backend_emu*.spl` composes RenderBackend calls, `portable_compute_emit` only emits text), so a CPU reference would be a second copy of the algorithm.
  - **Metal** cannot run on Linux.
  - **When device execution is unblocked, carry over from Vulkan and the CPU composite:** the gate is per quad over the whole quad (opaque and on-surface over the untrimmed rect; off-surface reads as non-opaque), done by one work item looping over the quad (both backends launch once per quad); a gray cell inside an LCD quad uses `cr = cg = cb = alpha`; keep the `has_lcd` gate and the solid fast path; skip the bitmap atlas; take tables from `engine2d_lcd_s32_tables`, uploaded as one buffer per distinct text colour. OpenCL is far cheaper than CUDA (runtime-compiled text, no PTX regeneration or SHA pins, `font_atlas_composite_opencl_source`); CUDA needs the nvcc `--ptx` regeneration and the `FONT_ATLAS_COMPOSITE_CUDA_*` pins in `backend_cuda_font_ptx.spl`. The fix that unblocks both is in the Rust seed externs, a separate lane.
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
- **Not carried (known limits):** [a container's own y and auto height ARE now carried, see "containers carry a fractional start y down", 2026-11-17 below] PERCENT author vertical margins (`margin-block: 2.5%`, `margin-top: 5%`) are still not resolved against the containing-block width at all (the token parses as a whole px count; the vertical sentinel space is -999..-1 literal px and <= -1000 vh, so a width-relative percent needs a new field plus the containing width at every `resolve_vertical_margin_px` reader), negative em/rem vertical margins keep the old whole-px parse, flex/grid/contents/float-band margins stay whole px (flex main axis is another lane). h3 18.72px font size is still `i32`.
- **Author em/rem/fractional-px vertical margins now carry the fraction too (2026-11-17).** `_decl_vertical_margin_exact_milli` / `_decl_vertical_margin_milli` / `_decl_vertical_margin_px` (decl_apply) turn a non-negative `em` / `rem` / `px` / bare token into milli-px floored to 1/64 px and store it in `margin_t_milli` / `margin_b_milli` instead of clearing it; the whole-px field becomes round-half-up of it so every px-only reader stays within 0.5 px. Whole values (`1em` of 16, `10px`) keep milli = 0. Sites: `margin` shorthand (decl_apply `margin_t_v`/`margin_b_v`, fast path in `declarations.spl`), `margin-top`/`-bottom`, `margin-block` (now token-split: one or two values), `margin-block-start`/`-end`. `decl_apply`'s final Style takes `margin_*_milli_v` when the side was authored (`margin_*_pos >= 0`), the inherited fraction otherwise.
- **Trap — vertical `em`/`rem` margins were never resolved before this.** `margin_token_vh_px`, `margin-block` and `margin-block-*` used `parse_int`, which stops at the first non-digit: `0.7em` -> 0, `1.5em` -> 1, `1.3rem` -> 1 (only `margin-left/right` went through `_decl_font_relative_length_px`). So this is a correctness fix as well as a fraction carry; the pre-fix painted rows were 11 to 126 px off (cumulative) in the new spec. `margin-block: 1.3em` also hit a `parse_nth_int` quirk (it counted the digit run after the dot as a second value and set the bottom margin to 3).
- **Trap (resolved by the containers entry below) — test the 13px section on a whole-pixel start.** Before containers carried their start fraction a second section after a fractional-height section lost it (Chrome 171.09 vs Simple 170.x); the spec still gives `.a` an explicit `height:160px`.
- Spec: `test/01_unit/browser_engine/author_fractional_margin_chrome159_spec.spl` (10 cases, 0/10 on base, 10/10 now; Chrome y 12.1875 / 42.984 / 63.484 / 94.281 / 125.078 / 146.266 at 16px and 171.094 / 201.891 / 222.391 / 249.281 / 276.172 / 295.266 at 13px). No other pinned spec moved; the 1x catalog rows and the combo matrix (154 baselined ids) are unchanged (measured: every page equals its row, so no row was lowered).

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
- **Typed linear over a colour:** `draw_ir_adv`'s typed stops branch now fills `command.color` before `draw_gradient_rect_stops` (it painted a translucent linear over the page, not the box colour). **Gate:** gradient lists with a non-default `background-size` or a px `background-position` stay fail-closed (colour only); size/tiling per layer is still unimplemented. (Superseded: see "Per-layer background size / repeat / position for gradient lists" below.)
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
- **Was permissive, fixed 2026-11-17 (see "selector rule admission, strict"
  below):** unknown `:-webkit-*` pseudo-classes, a pseudo-class after a
  pseudo-element, a pseudo-element inside `:not()`, and `:nth-of-type(1 of p)`.
- **Gates at the fix (2026-11-17, Chrome 159.0.8154.6, seed `cargo-target-webrender-vk`):**
  matrix 979 cells, 88 mismatching (base 88, no change). Selector structural spec
  base 62/71 -> head 71/71. 25 nearby specs, no new failing names.
  `simple_web_html_layout_renderer_module_split_spec` "keeps every parser input
  below 128 KiB" was already red at base (`..._core_selectors.spl` 138,390 B),
  and this change grows the file to 147,903 B. Split the file before adding more.
- **Split done (2026-11-17, pure move, no logic edits).** Rule admission,
  rule indexing and cascade ordering moved to
  `simple_web_html_layout_renderer_core_rule_index.spl` (47,584 B):
  `CSS_KNOWN_PSEUDO_CLASSES`/`_ELEMENTS`, `selector_list_has_unknown_pseudo`
  and its helpers, the `selector_bucket_*` keys, `build_rule_buckets`,
  `style_rule_candidates`, the sorted-list merge helpers, `_part_specificity`/
  `_group_specificity` and the candidate / z-index / style-order sorts.
  `_core_selectors.spl` (104,598 B) keeps parsing and matching, plus
  `_canonical_compound` (called by `selector_group_parts`) and
  `selector_group_matches_node_parts` (writes the module-level `_sel_*` step
  budget, so it must stay beside it). Five helpers are used on both sides
  and are `pub` in `_core_selectors` (the rebuilt seed rejects importing a
  non-pub name): `_compound_base_tokens`, `_nth_of_offset`,
  `_comb_code_of_part`, `_parse_attr_test`, `PSEUDO_NTH_LAST_CHILD`.
  Import chain is now
  `core_types -> core_selectors -> core_rule_index -> core_css_rules -> core`;
  each layer `export use`s the one below with an explicit list, so a symbol
  moved between layers must also leave the lower list. Import
  `build_rule_buckets`, `style_rule_candidates` and the sort helpers from
  `_core_rule_index`, not `_core_selectors`. A new family file must also be
  added to the `names` list in
  `simple_web_html_layout_renderer_module_split_spec` (it compares the
  directory walk count to that list).
## File layout: paint / facade parser-input splits (2026-11-17)

Pure moves, no logic edits. Each original keeps its name and `export use`s
every moved name, so importers are unchanged. A moved set never imports its
original file (no cycles), and it carries no module `var`, no `nil` and no
`extern fn`.
- `simple_web_html_layout_renderer.spl` (facade, 179,572 -> 110,660 B) ->
  `_compose_support.spl`: hit-test index, scrolled layout, material
  witnesses, CSS animation scheduling, opacity nesting, GPU paint state.
  These stay in the facade: the nil-returning `_animation_computed_value` /
  `_animation_progress` and every function that calls them, the result
  classes, `SimpleWebRetainedLayoutPreparation`,
  `_simple_web_layout_compose_retained`..`simple_web_layout_compose_prepared`
  and `_simple_web_draw_ir_translate_command`. Contract specs read all of
  these by path.
- `_paint_primitives.spl` (179,717 -> 101,730 B) -> `_paint_gradients_text.spl`:
  gradient layers, border mitre, thin and TTF text raster, bidi, widget
  chrome. The `_ttf_*` cache `var`s and both `_isqrt_i64` copies stay.
  Re-exports now chain through three hops (facade -> paint_layout ->
  paint_primitives -> paint_gradients_text). The chain resolves:
  `simple_web_renderer_spec` passes 123/123.
- `_paint_layout.spl` (158,898 -> 84,286 B) -> `_paint_draw_ir.spl`: style
  props, text commands, gradient and background layers, replaced media, SVG
  shapes, checkables. `_html_draw_ir_commands` and `_html_draw_ir_visible`
  stay (path-read contract specs).
- **Not split:** `_decl_apply.spl` (164,991 B). `_apply_decls_without_grid_inner`
  is a single 153,985 B function, so any split cuts its body, which is a
  logic change.
- **When moving code, also move its path-keyed rows:**
  - `cpu_lane_hotpath_files.txt`: a new file joins the list next to its original.
  - `cpu_lane_hotloop_baseline.txt`
  - `fail_open_baseline.txt`
  - `text_len_unit_mix_baseline.txt`

## 2026-11-17 — selector rule admission, strict (four Chrome-drop cases)

- **Where:** `_selector_range_has_unknown_pseudo(sel, start, end, element,
  no_elements)` and `_css_pseudo_class_allowed_after(element, name)` in
  `simple_web_html_layout_renderer_core_rule_index.spl`. `element` is the
  pseudo-element the current compound follows ("" for none; reset by a
  combinator, replaced by the next `::x`); `no_elements` is set for the
  argument of `:not()` and `:has()` only (Chrome accepts
  `:nth-child(1 of ::before)`).
- **Chrome 159.0.8154.6 `<style>` probe table (2026-11-17)** for what may
  follow a pseudo-element: `::part()`, `::details-content`, `::picker()` take
  any known pseudo-class except tree-structural, `:has`/`:host`/`:scope` and
  the scrollbar states (`::part(x):state(x)`, `:checked`, `:open` accepted;
  `:first-child`, `:empty`, `:has(p)` dropped). `::-webkit-scrollbar*` and
  `::-webkit-resizer` take hover/active/enabled/disabled/window-inactive and
  the scrollbar states, not `:focus`. Any other `::-webkit-*`,
  `::file-selector-button` and bare `::cue` take only user-action classes
  (hover/active/focus/focus-visible/focus-within); `::cue(p):hover` is
  dropped. `::scroll-button()` adds enabled/disabled, `::scroll-marker` adds
  target-current/before/after. `::selection` takes only `:window-inactive`,
  `::search-text` only `:current`, `::view-transition-*()` only
  `:only-child`. `::before`, `::after`, `::marker`, `::placeholder`,
  `::first-line`, `::backdrop`, `::highlight()`, `::slotted()` etc. take
  none. `:is()`/`:where()` follow anything (their argument is forgiving);
  `:not()` follows only if its argument passes the same element table. A
  class, id or attribute after a pseudo-element drops the rule
  (`::before.a`).
- **`:-webkit-*` pseudo-classes Chrome accepts:** exactly `-webkit-any`,
  `-webkit-any-link`, `-webkit-autofill`, `-webkit-drag`,
  `-webkit-full-page-media`, `-webkit-full-screen`,
  `-webkit-full-screen-ancestor`. Dropped (probed): `-webkit-frob`,
  `-webkit-hover`, `-webkit-read-only`, `-webkit-full-screen-document`,
  `-webkit-animating-full-screen-transition`, `-webkit-autofill-*`, etc.
- **Trap — legacy single-colon pseudo-elements.** `:before`, `:after`,
  `:first-line`, `:first-letter` sit in `CSS_KNOWN_PSEUDO_CLASSES`, but
  Chrome treats them as pseudo-elements: `p:before:hover` and `:not(:before)`
  are dropped. The scanner promotes them to `element` when no pseudo-element
  is active.
- **Trap — the scrollbar states are valid on their own.** `div:horizontal`,
  `div:window-inactive` are accepted by Chrome, so they are now in
  `CSS_KNOWN_PSEUDO_CLASSES` (they used to drop the rule).
- **Still open (measured, not fixed):** `:-internal-*` is accepted wholesale
  (Chrome accepts `-internal-autofill-selected`, `-autofill-previewed`,
  `-popover-in-top-layer`, `-dialog-in-top-layer`, drops `-internal-foo`);
  pseudo-class arity (`:-webkit-any` bare, `:-webkit-autofill(p)` dropped);
  a combinator after a pseudo-element (`::before > p`); `::marker::before`
  ordering.
- **Gates** (seed `cargo-target-webrender-blend`, base `83bb26da9b2` vs head, serial, failing NAMES compared): structural spec 83/97 -> 97/97 (14 fixed); parsed_equivalence 10/10, compound_any_order 9/9, of_type 7/7, selector_helpers 12/12, selector_matching 58/58, attr_select 11/11, nth_child_of_selector 28/28, selector_hardening 42/42, structural_pseudo_class 114/114 on both; simple_web_renderer 106/123, `_coverage_spec` 37/39 and module_split 1/3 fail the same names on both (0 new); combo matrix 979 cells, 88 mismatching on both, identical id set.

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
- **Superseded 2026-11-17 (see the "8 px (and 6 px) text" entry at the end): the cause was the x-height round-up, not pen phase.** Earlier note: `simple_web_renderer_spec` "uses explicit line-height for wrapped text layout" pins the darkest ink px (`0xFF352A44` x 2). Hinting now gives the 8 px caps Chrome's 6 rows, but that pin is a pen-phase statistic (Chrome's L stem sits about half a pixel right of ours): text-box mismatch 711 to 709 px, sum of abs delta +1.3%, darkest px `0x283151` (Chrome `0x483E5F` x 1). Not strictly closer, so not re-pinned; the spec stays red until the 8 px pen phase is fixed.
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
- **Follow-ups.** Multi-root Draw IR pages where any root holds text, a shadow or an outline still paint flat on cpu_simd/Vulkan (needs per-root text translation and halo padding). Nested groups: done, see the nested-group entry below. Translucent children on the raster: a translucent child over a transparent layer pixel gets alpha 255 (measured `166975` vs Chrome `1e7b9d`); cpu_simd/Vulkan match Chrome on that probe. Vulkan cost is now ~19 ms per 140x60 group (offscreen create 1 ms, render 15 ms, device restore 2-5 ms).

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

## 2026-11-17 — Gradient layers evaluated on the Vulkan device

- **Path:** `Engine2D.draw_radial_gradient_ellipse` / `draw_linear_gradient_line` -> (Vulkan primitive target, same precedence as `draw_image_blend`) `radial_gradient_device_tables` / `linear_gradient_device_tables` (`backend_emu`) -> `VulkanBackend.draw_gradient_layer_device` -> `shaders/gradient_layer.comp` (blob `backend_vulkan_gradient_layer_spirv.spl`, pin `scripts/check/check-gradient-layer-spirv-pinned.shs`, regen `scripts/tool/gen-gradient-layer-spirv.shs`). Any decline (empty tables, no pipeline, mask, buffer) falls back to the host evaluator + `draw_image_blend`, unchanged. Typed single linear layers (`emu_draw_linear_gradient_stops`) do not take this path.
- **Upload:** binding-1 tail = header (t_max, past-end colour, linear divisor, linear shift) + the host's own 1025-entry stop ramp + O(w + h) geometry terms. Radial: per-column u / per-row v (the host's clamped t16 axis values, `_emu_radial_axis_t16`, shared with the host evaluator). Linear: the projection split into per-column and per-row i64 terms whose sum is the host's `proj` exactly. Same 2-binding layout as `shadow_rect.comp` (the seed fixes bindings 0..2; no new binding).
- **Bit-exactness trap:** the seed's interpreter Vulkan device (`interpreter_extern/gpu.rs`) enables NO `VkPhysicalDeviceFeatures`, so `shaderInt64` is off and GLSL int64 is undefined. The kernel is 32-bit only: `(hi, lo)` uint pairs via `umulExtended` / `uaddCarry`, isqrt = float seed + exact integer correction (floor isqrt is unique, so it equals the host's seeded Newton), linear t = restoring 64/32 division after a `t_max * D` range check. The host declines when t_max > 4,000,000, len2 >= 2^48, or |proj| could reach 2^46. Proven bit-exact: device == `radial_gradient_pixels` / `linear_gradient_pixels` + the Chrome rule on translucent radial (t_max > 1), short-line (len2 < 2^32) and long-line linear layers (`backend_vulkan_device_gradient_spec`).
- **Composite:** Chrome's layer rule `round(s*a/255) + div255r(d*(255-a))` in ONE GLSL function, `chrome_layer_src_over`. Since #9993 (blend rounding, `a44733b2237`) the host image `blend` uses the same rule, and `backend_vulkan_device_glass_blur_spec`'s stack row (S1 / S2 / S3, previously 11,880 / 10,944 / 11,437 px off by exactly 1 level) passes unedited — but only on the rebuilt seed `cargo-target-webrender-blend` (sha256 `119feb0f865390b5...`); the older `cargo-target-webrender-vk` seed still carries truncating span kernels. Destination alpha < 255 (outside the rule): host straight-alpha src-over with rounded divides; vs cpu_simd 0 px over transparent, max 2 levels over a 50% destination.
- **Counters:** `vulkan_device_gradient_count()` (backend_vulkan, in the material census) rises per device layer; `engine2d_host_gradient_eval_count()` (engine) counts host evaluations and must stay put on Vulkan.
- **Declines (fail closed, host evaluator paints the same pixels):** a set mask (the kernel has no mask input) and geometry past the 32-bit kernel's range (`*_device_tables` return `[]`: t_max > 4,000,000, linear len2 >= 2^48 or projection >= 2^46). A clip is NOT a decline: `_finish_image_composite` honours it on the device. Rows in `backend_vulkan_device_gradient_spec` (masked, out-of-range linear, clipped), each shown red by removing its guard.
- **Trap — the blend seed rejects private imports in `run`:** on `cargo-target-webrender-blend` a hybrid `simple run` of a page dies (observed at base and head) on `private fn gradient_corner_dir_q16 ... is not visible` (and 2 more); `SIMPLE_EXECUTION_MODE=interpreter` runs. Same root as the 21 known private-import spec failures.
- **Perf (lavapipe, interpreter mode, blend seed, median of 3 processes x 3 renders):** `10-radial-gradient.html` 640x480 Vulkan steady render 4966 -> 1629 ms, process 15.91 -> 6.67 s, max RSS 739 -> 731 MB; cpu_simd shares the refactored table-driven host evaluator (`_emu_radial_axis_t16`): 7645 -> 7510 ms (-1.8%, base spread 7622-7651 ms, so outside run-to-run noise), 25.4 -> 25.6 s process, RSS flat at 669 MB. Numbers and identity in the bug file.

## 2026-11-17 — form-control sizing follows Chrome 159 ("all same as chrome")

Follow-up to the four 2026-11-16 behaviours. Each item has a `*_chrome159_spec.spl` with a lavapipe Vulkan device-readback row.

- **Authored checkbox/radio size, `type=image`, `<select>` border-box** (`form_control_authored_size_chrome159_spec`). Layout (`..._layout_engine.spl`, form-control branch) uses `css_outer_width/height` of an authored size and keeps 13 only for auto. Paint (`fb_input_accent_control_clip` and `_html_draw_ir_checkable_commands`) draws a square of side min(w,h) centred in the border box; Chrome 159 inks a 40x16 checkbox at (4,3) as columns 16..31, rows 3..18. A 13x13 box paints exactly as before. The UA decls (`form_control_ua_box_decls`) give `image` no border and add `box-sizing:border-box` to `<select>`. `<textarea>` stays content-box. **Trap — moving one control's height moves every later y in the fixture.** Pin x,y and the size together, from the same Chrome page.
- **Trap — an oracle page without `<!DOCTYPE html>` is QUIRKS mode (adopted 2026-11-17).** In quirks mode Chrome 159 makes `<textarea>` and text/password/email `<input>` border-box. In standards mode a `width:40px;height:16px;padding:2px` textarea is 46x22 and text/password/email are 48x24 content-box; search, button, submit, reset, checkbox, radio and select stay border-box. The abandoned lane pinned quirks values, and its textarea border-box broke `line_strut_baseline_chrome159_spec` AC-8 (Chrome standards: 106x46 textarea). This renderer has no quirks path, so start every oracle page with the doctype and pin standards values. Open: #9859 made text/password/email border-box from a quirks-mode reading, and `input_ua_box_sizing_chrome159_spec` still pins those rows on a doctype-less PAGE. See the bug record.
- **Glyph lookup by text uses codepoints** (`glyph_lookup_codepoint_chrome159_spec`). `glyph_index_for_char` / `glyph_rows_for_char` / `_glyph_charset_index_of` in `common/ui/glyph_bitmap_5x7.spl` now decode the one codepoint with `text_codepoints` (bounded by `byte_len() <= 4`) instead of gating on `ch.len() == 1`. **Trap — on the current seed `text.len()` counts CODEPOINTS** (`"•".len() == 1`, `byte_len() == 3`, measured 2026-11-17), so the old gate did not misfire there and the spec is 4/4 on base too; it is a guard for the owner-approved byte-unit `len()` (text slice units = bytes), under which the gate sends `•` to the unknown box. Do not cite "len() counts bytes" as current seed behaviour.
- **Password disc advance** (`input_password_mask_chrome159_spec` AC-6). `input_text_glyph_advance(nd, st)` (`..._paint_raster.spl`) is the ONE advance for an input value: the face's U+2022 advance (`resolve_font_metrics_with_language` at 10x size, rounded; 8px Arial 2.80 -> 3) for a masked password, else `style_text_advance`. All four consumers take it: the raster walk, `input_text_paint_plan` measured width, `input_text_visual_map` (carets) and the overlay plan. **Trap — the Engine2D page frame does NOT reuse the CPU raster for text:** it executes the Draw IR `_value` text command with `eng.draw_text` at the cell advance, so changing only the raster broke "Engine2D == software". The producer now adds `bitmap-glyph-advance` to that command when the advance differs from the cell, and `_engine2d_draw_ir_bitmap_text` (`engine2d/draw_ir_adv.spl`) steps each codepoint by it. Chrome's three 8px discs ink 3..10; the engine inks 4..12 (the disc cell `01110` starts at cell column 1).

## 2026-11-17 — horizontal-stem edge snapping (FreeType light autohinter, y)

- **Measured Chrome rule (Chrome 159, Liberation Sans/Serif, 12-24 px, H/e/A/digits grid, per-row coverage vs Simple):** stem WIDTH is not adjusted (light mode): thickness stays the scaled outline width (H bar 1.31 px at 16, A 1.22, e 1.03). Only position is fitted: stems of 1..1.5 px put their centre on k+26/64 (H16 bar = 5.75..7.06 px above baseline = one full row + a quarter row), <=1 px on k+1/2, >=1.5 px an edge on a row boundary (H20 bottom 6.40 / top 8.0; H24 8.0..9.875). A stem edge on a blue zone keeps the zone fit and its partner follows at natural width. e's bar anchors on the baseline overshoot (shift +0.16 px).
- **Trap — Chrome coverage is quarter-row quantised** (Skia 4x supersampling): bar rows read 0 / bfbfbf (0.25) / 77 (0.53) / 37 (0.78). Row coverage cannot tell edge rules apart within 1/8 px; compare sample counts, not "thickness".
- **Code (`sfnt_glyf.spl`):** `_hstem_segments/_hstem_pairs` (mutual nearest opposite-direction near-horizontal line runs, incl. the CLOSE edge, |dy|*14<=|dx|), `_hstem_knots` (per-glyph knots merged into the cached size knots, 26.6 integer FreeType arithmetic), wired in `sfnt_render_glyph_lcd`. Never stored in `_lcd_hint_cache`. Also: the x-height fit ratio now uses FreeType's rounded 26.6 values, and `_lcd_accumulate_row` takes Skia's tie rule (sample on an edge: top excluded, bottom included).
- **Not done:** round (curve) extrema are not stems; diagonal-stem points (7, 4 legs) only get linear interpolation (7 at 12/14/18 px 1-2 px worse); Simple's 4 row samples cannot give Chrome's exact thin-bar coverage (serif H16 0x3f vs 0x37).
- Probe (9 configs x 15 glyphs, delta>24 px): 3685 -> 3079 mismatching (-16.4%); H 132->36, A 219->106, 4 284->90, e 311->243. Catalog 1x: overview 1.29, html 4.68, css-layout 3.12, css-paint 3.67, forms-media 4.04, animation 3.59, evidence 0.77, tab-bar 0.42.
- Spec: `test/01_unit/browser_engine/glyph_hstem_snap_chrome159_spec.spl` (3 cases, red 0/3 on base). Re-pin: `simple_web_renderer_spec` 8 px darkest ink 0xFF283151 x3 -> 0xFF1B2A4B x1 (Chrome 0xFF4B3E5A x1); whole-image mismatch vs Chrome 419 -> 412 px, summed delta 52,265 -> 50,769.
- **Unconfirmed observation:** one early probe (a grid of `<div style="position:absolute;...line-height:24px">` glyphs, 320x100 page, seed cargo-target-webrender-vk 2026-11-14) showed Simple text 4 rows below Chrome, and the same grid as `<p>` did not. A later lane could not reproduce it on 16 minimal variants, and my first run may have compared against a stale PPM (the render had hit the 10 s watchdog). Treat it as unconfirmed, not a bug.

## 2026-11-17 — percent vertical margins resolve against the containing WIDTH

- **Rule (CSS 2.2 8.3, Chrome 159):** `margin-top` / `margin-bottom` / `margin` / `margin-block` percentages are of the containing block's content WIDTH (never height), floored to the 1/64 px LayoutUnit, and then ride the fractional block cursor like the author em margins (#10008 / #9951). Before: `2.5%` parsed as 2-3 px and no width was consulted.
- **Encoding:** a non-negative `N%` / `N.M%` is stored as a NEGATIVE `Style.margin_t_milli` / `margin_b_milli` = -(percent x 1000) (`_decl_vertical_margin_percent_x1000`, called first in `_decl_vertical_margin_milli`, decl_apply). Every parse site already routes through `_decl_vertical_margin_milli` (margin shorthand, `margin-block`, `-block-start/-end`, `margin-top/-bottom`, the `declarations.spl` fast path), so no parse site changed. The whole-px `margin_t`/`margin_b` keep their legacy value for px-only readers (flex/grid/float/inline-baseline paths still see the old whole-px guess for a percent).
- **Resolution:** `block_margin_milli(st, top, viewport_h, containing_w)` (layout_foundation) turns a negative milli into `floor_1/64(containing_w * pct / 100)`. The four block-flow callers in `layout_with_style_flow` pass the parent's content width `iw`; the `<body>` self-margin sites pass `viewport_w` (the html content width). Flex, grid, float and inline-baseline readers of vertical margins are NOT percent-aware yet (they read the legacy whole px).
- **Trap — percent margin escapes through a padding-less parent:** a child's top margin collapses through a parent with no padding/border, so the box that moves is the PARENT; its `getBoundingClientRect().y` is the one to compare. Give the oracle container `padding-top:1px`.
- Chrome oracle (headless `--dump-dom` + inline script, `.w{padding-top:1px;height:160px}` containers of width 300/333/450): `margin-top:2.5%` y = 8.5 / 170.3125 / 334.25; `margin:3% 0` second block 27.5 / 190.296875 / 357.75; `margin-block:1.5%` third 46.5 / 210.28125 / 381.25; nested `.in{width:200px;margin-top:3%}` in a 400 px content box + `margin-top:5%` child = 507.
- Spec: `test/01_unit/browser_engine/percent_vertical_margin_chrome159_spec.spl` (11 cases, red 0/11 on base, green 11/11).
- Catalog 1x: animation 3.59 -> 3.52 (row lowered), every other page unchanged (overview 1.29, html 4.68, css-layout 3.12, css-paint 3.67, forms-media 4.04, evidence 0.77, tab-bar 0.42). css-layout simple_ms 65.8 s (base) vs 62.2 s (head), noise. Regression: simple_web_renderer 123, browser_renderer 131, box_geometry 68, round4 53, block-fractional 8, author-fractional 10, line-strut 8, margin/abs/flex chrome159 specs and web_device_scale all green, 0 failing names.

## 2026-11-17 — Per-layer background size / repeat / position for gradient lists

- **Representation:** no new Style fields. `decl_apply` rewrites a gradient list so every image layer carries its own shorthand tail, `<fn>(...) <pos> / <size> <repeat>`. The entry of each longhand list is taken cyclically, else the layer's authored tail (`gradient_layer_list_apply_longhands`). Painters read the tails (`background_gradient_layers` -> tile 0 rect in Q10 px plus repeat axes). All-default lists (size `auto`/`100%`/`cover`/`contain`, no px offset, any repeat) stay byte-identical, so the typed paths are unchanged.
- **Tiles:** `engine2d/gradient_tiles.spl` `gradient_tile_spans` is the ONE pixel-centre tile cutter (raster + Draw IR).
  - Raster: `gradient_layer_tiled_pixels` evaluates whole-pixel tiles once and copies them.
  - Draw IR: `background-gradient-layer-tiles` (scaled) + `background-gradient-layer-repeat` (unscaled), emitted only when a tile fails to cover the painting area. `draw_ir_adv` makes one Engine2D gradient call per tile, so the Vulkan kernel (#10006) sees each tile, or declines.
  - Spec: `test/01_unit/browser_engine/background_layer_tiling_chrome159_spec.spl`.
- **Chrome facts (k=4):**
  - Gradients re-evaluate per tile.
  - `auto` / `cover` / `contain` on a gradient = the positioning area; one-value size = height `auto` = area height.
  - Default repeat tiles into the border under the border-box clip.
  - A fractional tile edge BLENDS the straddling pixel (open): keep pinned tiles on whole device px.
- **Trap — typed path dither:** a single tail-less gradient with `no-repeat` must stay on the typed path (`gradient_layer_list_apply_longhands` returns ""). The layer path has no ordered dither, so rerouting it moved `browser_renderer_spec`'s Chrome-pinned no-repeat rows by 1 LSB.
- **Trap — the spec helper's div vs frame size:** a bordered page's frame (48x40) is not its div (40x32). Passing the frame size as the div size made a correct render look like a 7-channel miss.
- **Trap — stdlib from scratch:** `simple run <scratch>.spl` cannot resolve `std.*` ("resolves from the project stdlib roots only"). Put probes in a temporary `test/` spec inside the worktree, and dump frames with `std.sffi.io.file_write_text`; failure messages are truncated.
- **Fail-closed (colour only):** `space`, `round`, 3/4-value positions, tail boxes / `fixed` / colours inside an image layer, a radial with a px/em radius on a fractional-size tile, and any layer above `BACKGROUND_GRADIENT_TILE_CAP` (1,024 tiles, `(area/tile+2)` per repeating axis) so a sub-pixel size cannot issue unbounded per-tile work.
- **Perf (640x480 page, two tiled layers: 40x40 linear + 64x48 radial at 10px 10px = 313 tiles; `simple test` process wall, median of 3, `/usr/bin/time -v` under `systemd-run MemoryMax=8G`, blend seed sha256 119feb0f865390b5... (60799992 2026-11-17 16:01:56.6), host load ~13-15):**
  - cpu_simd: base 16.0 s (colour only, fail-closed), head 64.2 s; an untiled head twin (same two layers, no size) 52.4 s. Tiling overhead is +11.8 s (+23%): one host LUT plus one evaluation per tile.
  - Vulkan (lavapipe): base 13.4 s, head 29.4 s, untiled twin 14.5 s. Tiling overhead is +14.9 s (~2x): one device dispatch per tile, ~48 ms each.
  - Max RSS 0.95-1.0 GB on every lane, base and head (one ~0.24 GB run in most triples).
  - Follow-up (perf, filed here): evaluate a whole tile grid in ONE Vulkan dispatch (tile-local coordinates in `gradient_layer.comp`), and reuse one host tile on cpu_simd when tiles are pixel-aligned.
## 2026-11-17 — html catalog page classified; `<a>` needs href for the UA link style

- **Classification (32,034 px = 4.68%, full table in `doc/08_tracking/bug/web_render_html_page_residual_2026-11-17.md`):** glyph residual ~67%, one-row drift below the flex `<article><header>` 24.5% (Chrome header 97.52 px high, Simple 98, article start rounded to 121 vs 120.81), fractional h3 18.72 px ~7.5%, card corner AA 0.25%, `<a>` link style 0.43%.
- **Fixed:** `tag_defaults` painted every `<a>` blue + underlined; Chrome's `a:-webkit-any-link` needs `href` (empty `href=""` counts). The style pass in `core.spl` restores the inherited `fg` / underline for an `<a>` without `HNODE_ATTR_HREF_BIT`. Spec `anchor_without_href_chrome159_spec` (red 2/4 on base). html 4.68 -> 4.66; the catalog feature list holds hundreds of `<a>` examples but only one is inside the 760 px viewport, so the page gain is small.
- **Trap (both halves now landed, see "containers carry a fractional start y down") — the drift needs BOTH known limits fixed.** A fractional flex-container height alone gives 121 + 97.52 = 218.52 -> 219, Chrome 218.33 -> 218. The container's start fraction (120.81) must reach its children as well. Do not land one half.
- **Trap — `tag_defaults` sees only the tag.** Anything in Chrome's UA sheet keyed on an attribute (`a[href]`, form `type`) is applied in the `core.spl` style pass, ahead of author declarations, using `nd.attr_mask` hot bits.
- **Method note:** the scratch tools (band histogram, dy-credit, pixel probe) are `.spl` scripts run with `SIMPLE_EXECUTION_MODE=interpreter` from the repo root (imports resolve from the cwd); `cli_get_args()` includes the script path as `args[0]`.


## 2026-11-17 — Nested CSS opacity groups match Chrome 159 (raster, cpu_simd, Vulkan)

- **Chrome's rule:** every level is a layer. An inner group restores into its parent's transparent premultiplied layer with the same SkBlendARGB32 rule, in tree order. Nothing is folded, even when an outer group's only item is the inner group: `0.5{0.5{red,green}}` over gray gives `a06060`/`60a060`. A premultiplied model reproduced all 37 sampled cells before any code was written. A straight-alpha layer is safe: `premul(unpremul(P,A),A) == P` for every `0 <= P <= A <= 255` (exhaustive).
- **Draw IR producer** (`simple_web_html_layout_renderer.spl`):
  - `_simple_web_fractional_opacity_command_roots` returns `root_parent`. A root may nest up to level 2 (`_SIMPLE_WEB_OPACITY_NEST_MAX_LEVEL`), because the executor's `ENGINE2D_DRAW_IR_EMBED_MAX_DEPTH` is 3; deeper nesting turns surfaces off.
  - No root may be re-entered after its subtree's run closed.
  - Bounds fold each command into its root and every ancestor. A root that holds or is a nested root is always a group (`bounds.group`).
  - There is one batch per top-level root. A nested command is moved into its innermost layer and tagged `css-opacity-group-nest` = `root,x,y,w,h,milli` per level, outermost first, each rect relative to its parent layer.
  - Only top-level layers count toward the one-viewport surface budget; every level must be translatable.
- **Executor** (`draw_ir_adv.spl`): `_engine2d_draw_ir_render_css_group_layer` cuts a group layer's commands into runs by nest entry `depth`. A plain run paints into the layer; a nested run becomes a group batch rendered through `_engine2d_draw_ir_render_batch_embedded` at `depth + 1` (fresh offscreen, restore into the parent layer). On Vulkan the device kernel restores into a translucent parent layer too: `css_group_restore.comp` already has the `da < 255` branch, so no shader change was needed. Measured: 18 device restores (8 top-level + 10 nested), no fallback.
- **Trap: device scale.** `draw_ir_composition_at_device_scale` must scale the nest prop's x/y/w/h (`_dir_scale_opacity_nest`). Without it, k=4 drew inner layers at 1x offsets (worst error 104 levels).
- **Raster** (`paint_raster.spl`): `_raster_layer_passes` paints a group's layer. If the layer holds nested groups, it holds back the nested groups plus every positioned box after a nested group that overlaps it ("late" subtrees). It paints the rest, then interleaves the nested restores (`_raster_restore_group`, recursive) and the late subtrees in tree order. Inside a layer, one painted item is already a nested layer (`min_painted` 1). A group whose subtree mixes nested roots with text or z-index stays on the per-element path.
- **Pins** (`opacity_group_chrome159_spec`): 37 Chrome cells × raster, cpu_simd and Vulkan, including 3 levels, overlapping sibling inner groups and a box after an inner group that overlaps it. The k=4 full frame of 3 blocks is pinned exactly (dev 0): this page has no tile-seam deviation in Chrome.

## 2026-11-17 — Raster opacity groups with translucent, shadow and gradient members (two-pass layer)

- **Mechanism.** The raster blenders ignore destination alpha and write 255. A layer with non-opaque members is therefore painted twice, both times with the members' positions intact:
  - **B** over opaque black. Its colour channels are exactly Chrome's premultiplied layer colour, for every Chrome rule (solid, image, coverage).
  - **W** over opaque white.
  - Layer alpha = `255 - (W - B)` (green channel), and colour = B divided back out (`_raster_group_layer_from_passes`).
  - Opaque-only layers keep the single zero-initialised pass. The 12-group page does not change.
- **Exact only for disjoint non-opaque paint.** Each rule's white-backdrop term is exactly `255 - a`, so alpha is exact for one non-opaque paint per not-yet-opaque pixel, plus any number of opaque paints. A model checked this: 40000/40000 random restricted sequences exact; unrestricted, 12% are off by ±1 after the restore.
  - Admission (`_raster_group_node_translucent_items`): a layer's non-opaque paint rects (shadow extent, translucent bg/border/outline, non-opaque gradient or image layer, img) must be pairwise disjoint, at most one per node.
  - A two-pass layer may not hold nested groups.
  - Otherwise the group stays on the per-element path. Open: two translucent boxes overlapping (Chrome `E3D994`) and image plus translucent black (`9A9FBC`). The general fix is a white-forced alpha pass at every raster pixel-write site.
- **Trap: B must start opaque black, not 0.** Gradient layers go through Engine2D `blend`, which honours a transparent destination and leaves straight colour (measured `1ca569` vs Chrome `24b05e`).
- **Trap: shadow extent.** The tile pad `_paint_shadow_pad` (+8, symmetric) made a shadow group overlap the next row of cells and fail the overlap rule. `_raster_group_shadow_extent` is directional: offset + spread + 2*blur per edge.
- **Ops now counted like Chrome:** shadow, img and gradient or image layers are paint ops of their own.
- **Gap, not caused here:** the raster lane paints a plain `<img>` only with the widget image class, so image members contribute nothing on the raster. The pin for that pixel is left out.
- **Pins:** `opacity_group_chrome159_spec` row "translucent, shadow, gradient and image members on the CPU raster", 19 exact cells plus the dithered gradient block (Chrome's own `24b05e`/`24b15e`).

## 2026-11-17 — Multi-root opacity pages with shadow, outline and text roots (cpu_simd, Vulkan)
- **Was:** on a page with 2+ opacity roots, every root needs a bounded translated surface. A root with a shadow or outline (halo past the command rect) was marked untranslatable, which declined surfaces for the WHOLE page: every group painted flat (no opacity).
- **Halo** (`_simple_web_opacity_halo`, producer): the root rect grows per side by each outset shadow's offset toward that side + spread + 2*blur, and by outline width + |offset|. A shadow length that is not px returns `[]`, and the root stays untranslatable (declined, as before). Symmetric growth was tried first and overlapped the neighbour cells, which blew the one-viewport admission budget.
- **Text roots:** on this page the text command has no glyph run, so it is translatable. A text root needed only the halo fix, plus the `pub` fix below. A root with a real glyph run (`glyph_run.valid`) is still untranslatable and declines surfaces for the page. That case is open: no pinned page produces one.
- **Group count:** a gradient or image background paints from the style (the command colour is 0), so the producer counts it as a paint item once per owner, like `_raster_group_node_ops`. Without this the group folds, giving ±1.
- **Trap:** small text on cpu_simd and Vulkan needs `sfnt_render_glyph_lcd` to be `pub` (upstream `08486feffd2`, cherry-picked). Without it every text page dies with a semantic error under the seed.
- **Pre-existing, unpinned:** no lane paints an `outline` on a positioned box or this `<img>`. Chrome draws the same 3px 50% shadow as `5F5F5F` on a 10x8 box and as `606060` on an 8x5 box; Simple gives `606060` on both. Engine2D gives +1 green where two translucent paints overlap.
- **Pins:** `opacity_group_chrome159_spec` has 3 rows: `tg_page` and `mr_page` on cpu_simd and Vulkan against Chrome, plus the text root on the multi-root page equals the text root alone (Simple-internal glyph check).


## 2026-11-17 — Coverage lane: sfnt_glyf public API and browser face line metrics
- **Measurement trap:** `simple test <dir> --coverage` does not work on the blend seed. Every spec aborts with "coverage instrumentation wrapper failed to compile ... NEVER run under the requested coverage path". Use name-reference function coverage (`doc/08_tracking/test/web_render_coverage_2026-11-17.md`) as a lower bound only.
- **Pins:** `sfnt_glyf_public_api_spec` (raw-byte oracles: table directory, hmtx advance * size / unitsPerEm). `browser_face_line_metrics_chrome159_spec`: normal line height equals Chrome at 12/16/24/32/48px for serif, sans-serif, monospace; ascent equals Chrome except 48px serif and sans-serif.
- **Gap:** Chrome baseline at 48px is 44 for serif and sans-serif, Simple returns 43 (`browser_face_ascent_descent_px`). Bug: `doc/08_tracking/bug/browser_face_ascent_48px_off_by_one_2026-11-17.md`.
## 2026-11-17 — percent vertical margins in flex, absolute, float and inline-block layout

- **Gap:** #10039 stored a percent vertical margin as a negative `margin_t_milli` / `margin_b_milli` and only the block-flow callers resolved it. The other paths read the whole-px `margin_t` / `margin_b`, which for a percent held the bare number (`margin-top:4%` read as 4 px).
- **Fix:** `vertical_margin_px_in(st, top, viewport_h, containing_w)` (layout_foundation) floors a percent margin to whole px and leaves every other form on `resolve_vertical_margin_px`. `style_with_resolved_percent_margins(st, containing_w, viewport_h)` returns a copy with `margin_t` / `margin_b` resolved and the milli cleared. Applied in `flex_item_percent_style`, the column-flex measure / base / placement styles, `absolute_child_style` and the `absolute_child_y` / static-position callers (containing width = padding box), float margins, inline baseline margins and the `display:contents` child loop.
- **Chrome oracle (300 px containers):** flex row item `margin-top:4%` y 12; abs box in a 200 px + 2x20 padding relative parent `margin-top:5%` y 12 (5% of the 240 px padding box); float `margin:3%` x 9 y 9; inline-block `margin-top:2%` y 6; flex column item `margin-top:4%` y 12, next item y 22.
- **Horizontal percent margins** (`margin-left:5%`) already resolved through `resolve_horizontal_margin_px`; no change.
- **Still open:** grid items (percent of the grid area width, `grid_margin_t` still reads whole px); `vertical-align:top` inline-block ignores `margin-top` even in px (Chrome offsets by it).
- Spec: `test/01_unit/browser_engine/percent_margin_contexts_chrome159_spec.spl` (5 cases, red 0/5 on base, green 5/5).
## 2026-11-17 — Glyph grayscale raster: scanline sweep (perf, byte-identical output)
- **Was:** `_glyf_edge_coverage` tested every outline edge for each of the 16 samples of every pixel (pixels x 16 x edges) and `rasterize_sfnt_glyf` pushed one byte per pixel. Large glyphs (64 device px on the dpr4 catalog) dominated render time.
- **Now:** `_glyf_raster_alpha` (`src/lib/common/encoding/sfnt_glyf.spl`) gathers each sample scanline's edge crossings once, insertion-sorts them and sweeps the 4 sample x positions of each pixel with one pointer; the buffer is preallocated. Same crossing expression, `<=` test and integer winding sum, so every coverage byte is unchanged. Used by `rasterize_sfnt_glyf`, `sfnt_render_glyph_into` and `sfnt_rasterize_glyph_baseline_aligned`.
- **Proof:** Simple PPM sha256 equal on base and head for all 8 catalog pages at 1x and css-layout at 4x. css-layout wall: 1x 62s -> 49s, 4x 324s -> 158s (peak RSS 2.82 GB -> 2.91 GB at 4x).
- **Not changed:** the LCD path (`_lcd_accumulate_row`) is already a per-row crossing sweep; its extra cost is the 3x subpixel columns plus the FIR, not a per-pixel edge scan.

## 2026-11-17 — Gradient polish: length stops, rounded gradient lists, canvas propagation (Chrome 159)

- **Length stops (`px`, `em`):** `parse_gradient_stops_on_line(raw, line_q10, em_px)` (foundation) parses each stop as unset / percent / length (`gradient_stop_token`), resolves lengths to permille of the layer's gradient line (rounded), then runs the CSS fix-up with a separate `placed` flag (a resolved negative position is not "unset"). `parse_gradient_stops(raw)` = line 0, so %-only lists are byte-identical. `background_gradient_layers` resolves per layer AFTER its tile geometry: linear = |end - start| of the line, radial = the gradient ray (`rx`). `em` = the element's `font_size` (passed by all 4 callers). Kernels and the Vulkan shader are untouched: the device tables carry the host LUT, so the stop unit never reaches the shader.
- **Trap — typed paths parse at cascade time** (no box): `gradient_has_length_stop` makes `_background_is_exact_typed_linear_layer` and the three typed-radial branches of `decl_apply` decline, so those gradients take the list path (same move as the `transparent` trap). `gradient_stop_color_text` now strips a length too (`#f00 10px` used to parse as no colour). Negative percentages used to read as positive (`-20%` -> 200); `rem` stays unpositioned (no root font size there).
- **Rounded boxes:** Chrome clips the WHOLE background once (`two.png` == solid fill within 1 level), so per-layer coverage is wrong (two opaque layers compounded the corner alpha, 260 px off the solid fill). Raster `fb_gradient_layers_round_clip` and Draw IR (`elif layered:` in `draw_ir_adv`) build ONE image of the clip rect: box colour, then each layer via `gradient_layer_stack_over` (Engine2D `blend`, transparent start), alpha scaled once by `gradient_pixels_round_clip` (`engine2d/gradient_tiles.spl`, the solid fill's `_emu_corner_cov256` formula), one `draw_image_blend`. Vulkan composites that host image on the device (the kernel has no coverage input). Radii: `background_gradient_clip_shape` (border-box radii minus border/padding insets of the clip box), Draw IR prop `background-gradient-layer-clip-radii` (device-scaled). The typed-nonuniform branch no longer pre-empts a layered box.
- **Chrome corner AA is NOT our formula:** on a flat rounded fill Chrome differs from `_corner_coverage256` by up to 57 levels at partial-coverage pixels (five fitted models — exact area, 4 sub-rows, Skia supersample, distance with radius offset — all leave 34-64). Gradient corners inherit that residue and no new one; pin only fully inside/outside corner pixels.
- **Canvas propagation outside widget mode:** `canvas_gradient_source` = html when it has any background, else body; it must carry a gradient list, a typed radial (raw kept) or a default-geometry typed linear. Positioning area = the html box (Chrome: `body{margin:4px;height:20px}` repeats every 28 CSS px from the canvas top), painting area = `canvas_background_extent`. That node's own box background is suppressed (raster `_paint_passes` pass 1; Draw IR `_html_draw_ir_root_canvas_gradient` zeroes the command colour and re-resolves the layers). Widget mode is untouched.
- Spec: `test/01_unit/browser_engine/gradient_polish_chrome159_spec.spl` (12 rows incl. Vulkan == cpu_simd rows and a device-kernel row for length stops).
- **Full frame vs Chrome (k=4, max per-channel / px > 2):** px/em/radial/tiled length-stop pages max 1-2, 0 px; body propagation pages max 1-2, 0 px; rounded uniform page max 61 at 277 px, all within 1.5 px of a corner arc; per-corner padding-box page raster max 54 (472 px: the raster double-blends a translucent border's square corner), cpu_simd max 131 (1705 px: the Draw IR lane paints a per-corner-radius box's border as a square band). Vulkan == cpu_simd on all 8 pages (0 px).
- **Open:** Chrome rrect corner coverage model. (Re-measured 2026-11-19 on page 6: raster and cpu_simd both 235 px, all at the three rounded corners; the Draw IR per-corner band and the raster double blend are closed.) (`rem` stops: fixed 2026-11-19, rewritten to px at cascade time by `gradient_rem_stops_to_px`; pinned by `gradient_rem_stops_chrome159_spec`.)
## 2026-11-17 — 8 px (and 6 px) text: x-height fits down, not up (`_lcd_hint_knots`)
- **Was:** 8 px sans `l` / `H` / `x` / `d` were 7 / 6 / 5 / 7 rows against Chrome's 5 / 5 / 4 / 5 (+34% ink on the `l`). The earlier "L stem half a pixel off" note was NOT a pen-phase error: pen phases match Chrome to 0.03 px for `l` at 8, 10, 11, 12 px and `H` exactly; the residual was vertical.
- **Cause** (`src/lib/common/encoding/sfnt_glyf.spl`, `_lcd_hint_knots`): the x-height round-up (`increase-x-height`, threshold 52/64 for 6..14 ppem) was applied at every size. Measured rows in Chrome: 10 px rounds up (x-height 6 rows, H 8 rows), but 8 px (and 6 px) fit DOWN (x 4 / 3 rows) as if the 40/64 threshold were used. The round-up is refused when it would grow the em by 1.25 px or more: 10 px = 1.19 px (accepted), 8 px = 1.33, 6 px = 1.46 (refused). 7, 9, 11-14 px are the same either way. The 1.25 boundary is empirical, between 1.19 and 1.33 (FreeType's two-pixel cap over an effective max_height of about 1.6 em).
- **Not caused here:** the spec page in `simple_web_renderer_spec` has no `font-family`: Chrome draws it in Liberation Serif, the engine in the sans face. Whole-page mismatch against Chrome there is dominated by that (412 -> 426 px, 50,769 -> 63,370 summed delta). With `font-family:sans-serif` on both sides the same text goes 318 -> 106 px and 60,346 -> 7,607. Open: default font family should map to serif.
- **Pins:** `small_text_vertical_hint_chrome159_spec` (3 cases, red on base): ink rows l 11..15, H 11..15, x 12..15, d 11..15, p 12..17 equal Chrome's; `l` stem x=5 `0x77BFEF` is Chrome's byte, x=4 `0xD7975F` (Chrome `0xCF8F5F`); H bar row 13 (engine `0x778787`, Chrome `0x6F7777`). `simple_web_renderer_spec` 8 px darkest ink `0xFF1B2A4B` -> `0xFF42375F` (Chrome `0xFF4B3E5A`).
- **Trap:** the per-glyph centroid trick (split ink by empty columns) finds pen-phase errors fast: `l l l …` gives per-glyph centroids to 0.02 px. Row sums (ink per row per glyph) found this bug; an `l` that is 2 rows too tall is invisible to centroid x.
## 2026-11-17 — containers carry a fractional start y down and a fractional auto height up

- **Fixed the two "Not carried" known limits of the block-axis margin entry (a container's own y was rounded before its children started; its auto height dropped the residual).** `layout_with_style_flow` now takes a start fraction through `g_origin_frac_milli` (set by the caller right before `layout_with_style`, read and CLEARED at flow entry so it cannot reach another box) and seeds `cy_frac` with it instead of 0. It returns the cursor residual at its bottom edge in `LayoutResult.end_frac_milli` / `end_frac_valid`; the parent block loop sets `cy_frac = child end frac` after `cy = cy + child_height`, so the next sibling continues from the TRUE bottom. Box edges stay rounded: top = round(true y), height = round(true bottom) - round(true y) (Chrome pixel snapping).
- **Single-line flex row.** A plainly placed item (child_y equals the whole-px formula, non-negative non-auto margins) starts at `cursor_advance_px(origin_frac, margin_t_milli)`, hands the residual to its own cursor, and contributes `margin_t_milli + (height*1000 + end_frac - item_origin) + margin_b_milli` to `flex_max_outer_milli`; the container height is `cursor_advance_px(origin_frac, flex_max_outer_milli + pads*1000)` and it returns the matching end fraction. With whole margins and heights this is byte-identical to the old `max_child_h + pads` (checked by the regression set below).
- **A box with an authored or clamped height** (`height`, `contain: size`, min/max/fill that changed it, `h < 1`) returns its START fraction, because its bottom is start + h exactly. A retopped child (its first child's margin collapsed through it, `offset_layout_subtree` by whole px) keeps the shifted end residual only while it stays in [-500, 500), else the parent keeps its own residual (old behaviour).
- **Spec:** `test/01_unit/browser_engine/fractional_container_origin_chrome159_spec.spl` (4 cases, 0/4 on base, 4/4 now; Chrome tops 10.5 / 31 / 74.72 / 123.44 / 159.44 / 164.44 flex 97.4375 / 199.16 / 261.875 pinned as painted rows).
- **Still not carried:** the flex-wrap and flex-column paths, grid, table and float-band containers return `end_frac_valid = false` (parent keeps its own residual) and start their children at 0; line heights are whole px (a 28.08 px line of an 18.72 px h3 is 28 here, so the html header is 97.44 vs Chrome 97.52, which still rounds to the same row; the rest of that gap is the `i32` font size).
- **Trap — the start fraction must be stored right before the call.** Any new `layout_with_style` call site that is NOT given a fraction gets 0 automatically (the flow entry clears the global), which is the old behaviour; a call that sets it and then does not reach flow would leak it to the next box.
- **Measured (blend seed, 1x catalog):** overview 1.29, html 4.66 -> 3.65 (row lowered), css-layout 3.12, css-paint 3.67, forms-media 4.04, animation 3.59, evidence 0.77, tab-bar 0.42. Animation 3.59 vs its 3.52 row is PRE-EXISTING (same 3.59 on a base worktree run side by side), not this change. css-layout simple_ms 57.1 s (base) vs 57.3 s (head). Regression: simple_web_renderer 123, browser_renderer 131 + 4 (two files), no grid chrome159 spec exists, box_geometry 68, round4 53, block-fractional 8, author-fractional 10, line-strut 8, percent-margin 11, every margin/collapse/abs/flex/float/grid chrome159 spec, web_device_scale 22, background_layer_tiling 9: identical pass counts on base and head, 0 failing; combo matrix 154 baselined ids unchanged, no new, no stale.

- Face ascent vs baseline (2026-11-18): Chrome's `line-height: normal` baseline = rounded ascent + floor(rounded line gap / 2). Serif/sans 48px: ascent 43, baseline 44. `browser_face_ascent_descent_px` returns the face ascent (43) and the strut adds the half-leading; do not "fix" the rounding. Pinned by `line_strut_baseline_large_chrome159_spec`.


## 2026-11-17 — parser-input file splits (foundation, layout_foundation, webgl_context)

Pure moves, no logic edits, to get files under the 110 KiB lane target (spec cap 128 KiB): Sizes are post-#10061 (gradient polish).

| original (before -> after, bytes) | new file (bytes) | what moved |
|---|---|---|
| `simple_web_html_layout_renderer_foundation.spl` 172,172 -> 109,515 | `..._foundation_values.spl` 66,197 | position-aware string find, nil-free CSS value parsers (color tokens, lengths, gradient stop pieces, transforms, line-height, nth-box, margin tokens, object-position), declaration-table readers, `decl_get`, `ws_tokens` (107 decls) |
| `simple_web_html_layout_renderer_layout_foundation.spl` 171,862 -> 105,686 | `..._layout_text.spl` 70,863 | text measurement, wrapping, intrinsic widths, replaced / form-control intrinsic boxes (92 decls) |
| `webgl_context.spl` 186,715 -> 93,867 | `webgl_context_objects.spl` 49,016 and `webgl_context_pipeline.spl` 50,610 | `WebGLContext` methods moved into `impl WebGLContext:` extension files |

- **Re-export pattern.** The original keeps its name and gains one `export use <new>.{every moved name}`. This binds locally and re-exports, so importers don't change. Re-exporting private (`fn`) names is accepted by the `cargo-target-webrender-blend` seed: verified on specs that import moved private names through the facade, with no new failing names.
- **The moved set must be dependency-closed.** Nothing moved may reference a declaration left behind, so the new file never imports the old one. Module `var`s stay with every writer. `g_text_first_line_dx*` / `g_text_line_boxes*` remain in layout_foundation, because layout_engine assigns them through its import.
- **WebGL uses the JsInterpreter precedent** (`nogc_sync_mut/js/engine/interpreter.spl`). Extension files `use webgl_context.{WebGLContext, ...}`, and webgl_context.spl ends with `use webgl_context_<x>.{WebGLContext}`.
- **Push gates count moved code as NEW** (base 0 for a new file). `check-nil-outside-unsafe-added` cannot be annotated, so declarations with `nil` outside `unsafe`, and every moved declaration that reaches them, stay in the old file. That is why the animation/transition validators, `parse_color*` and the gradient parsers are still in foundation. `check-primitive-api-added` takes `# reason: ...` + `# @allow(primitive_api)` above each moved `pub fn` that has bare primitives. Run both with `--changed origin/release/1.0.0..HEAD` before pushing.
- **Bookkeeping a move touches.** List every new `simple_web_html_layout_renderer_*` file in the `module_split_spec` names list, because the walk count must equal the list. Repoint source-contract specs that read a file by path (`web_jit_unique_names_contract_spec`, `baremetal_string_split_abi_spec`), keeping negative checks over both halves. Prune `private_import_baseline.txt` rows whose fn left the file (`check-private-import-baseline.shs --prune`). Relocate `cow_alias_hotpath_baseline.txt` rows by file and line.
- **Blocked: `simple_web_html_layout_renderer_layout_engine.spl` (233 KB).** `layout_with_style_flow` is a single 184,361 B function (line 960). It cannot go under the cap without cutting the function body into helpers, which is a logic refactor.
- **Still over 128 KiB:** layout_engine, the main facade, paint_primitives, decl_apply, paint_layout and core_selectors (other lanes).
## 2026-11-18 — inline-block `vertical-align: top | bottom | text-top | text-bottom` aligns the margin box

- **Was:** only baseline-aligned items entered `align_inline_line_baselines`; a top/bottom/text-* aligned inline-block stayed at its natural y and never grew the line, so `margin-top:6px; vertical-align:top` sat at y=0 (Chrome 6) and `margin-top:30px` left the line 18 px (Chrome 40).
- **Fix** (`simple_web_html_layout_renderer_layout_foundation.spl`, `inline_atomic_valign` + `align_inline_line_baselines`; caller in `..._layout_engine.spl` near the inline contribution): atomic inlines (display != inline, not text) with those four keywords join the line's alignment list with their resolved margins and are placed by MARGIN box (CSS 2.2 10.8). `top`/`bottom` hang from the line box and grow it by their margin-box height (a taller `bottom` box pushes the baseline down); `text-top`/`text-bottom` hang from the parent content area (`inline_content_area_ascent` / height) and enter ascent/descent. The border-box height no longer inflates `inline_line_h` for them.
- **Chrome 159 matrix** (default serif 16px, 20x10 box after "x"; y, line h): top mt6 6,18 mb6 0,18 6/0 6,22 mt30 30,40; bottom mt6 8,18 mb6 2,18; text-top same as top; text-bottom mt6 7,18 mb6 1,18 6/0 6,23 mt30 30,41. All 24 match.
- **Spec:** `inline_block_vertical_align_margin_chrome159_spec` (4 cases, 0/4 on base, 4/4 now).
- **Not done:** `middle` (needs x-height, Chrome lands on fractional y) — `doc/08_tracking/bug/inline_block_vertical_align_middle_ignores_margin_2026-11-18.md`. Plain `display:inline` elements with these keywords are untouched. A top item and a taller bottom item in the same line use `max` for the line and drop the baseline by the bottom growth only; not measured against Chrome.
## 2026-11-18 — Default font family is serif (Chrome 159)
- **Rule:** a page with no `font-family` computes "Times New Roman", which fontconfig maps to Liberation Serif. Form controls compute to Arial (Liberation Sans); code, kbd and textarea to monospace.
- **Change:** the default `Style.font_family` is now `serif`. The UA overrides are unchanged.
- **Pin:** `default_font_family_chrome159_spec`.
- **Trap:** any spec page that sets no family was being compared against Chrome's serif glyphs with our sans glyphs. Re-measure such pins against Chrome before reading their whole-image metric. On the 8 px wrapped page, mismatch went from 426 to 149 px.

## 2026-11-18 — Fractional computed font-size (Chrome 159)
- **Rule:** Chrome keeps `font-size` as a float. The UA h3 is 18.72 px, and `1.17em` or `117%` stay fractional. Run width, the `normal` line height and the strut all scale from the float.
- **Change:**
  - `Style.font_size` stays whole px, for the raster. `Style.font_size_milli` carries the fraction; 0 means whole px.
  - Helpers live in `foundation_values.spl`: `font_milli_of`, `font_milli_round_px` and `font_milli_store`.
  - Run advances are rescaled from an 8x reference size (`resolve_font_metrics_with_language_milli`).
  - Ascent, descent and gap are each rounded at the float size (`sfnt_line_metric_units_*_milli_px`).
- **Trap:** an exact .5 px size rounds DOWN for raster rows. Chrome's 13.5 px ink rows equal its 13 px rows.
- **Pin:** `fractional_font_size_chrome159_spec`.
- **Catalog 1x:**

| page | before | after |
|---|---|---|
| html | 3.65 | 3.51 |
| css-layout | 3.12 | 3.00 |
| css-paint | 3.67 | 3.55 |
| forms-media | 4.05 | 3.93 |

- **Rows tightened:** the four rows above. The animation row is untouched, because its measurement is noisy at 3.47-3.59.

## 2026-11-18 — Mid-line text run keeps Chrome's fractional pen origin (LCD phase)
- **Rule:** Chrome 159 lays a line out in fractional units. A `#text` run after an inline element starts at the exact sum of what precedes it. `<span>ll</span> l` at left:1 starts at `1 + 7.1094 + 4.4453 = 12.5547`, so its first glyph takes the 12.5 quarter phase. The inline loop is whole-pixel (pen 12 or 13), so every glyph in the run was painted at the wrong LCD phase. Chrome alone repaints 4,329 px of one forms-media `<li>` when its origin moves from .617 to .0.
- **Change:**
  - `Style.resolved_font_width_milli` / `resolved_space_milli` hold exact widths. They are set only for an unadjusted run.
  - The inline loop carries `inline_err_milli`, the exact-minus-integer error. It stays valid only while the cursor sits at the recorded (x, line); a line start is 0. See `inline_pen_err` and `inline_item_width_err_milli` in layout_foundation.
  - An exact advance is a one-line `#text` run, or a plain inline element with one such run. Anything else makes the error unknown, and the run keeps today's integer pen.
  - Each `#text` records `LayoutResult.pen_origin_milli` (`g_text_pen_origin_milli`, same lifecycle as `g_text_first_line_dx`). It is recorded only on left-aligned lines.
  - Draw IR carries the origin as the `pen-origin-milli` style prop on the single-line or first-line command.
  - `_lcd_apply_pen_phases(..., pen_origin_milli)` folds the origin into each glyph's quarter phase. A glyph with no phase cell takes a whole-pixel round shift, which is 0 when the origin is 0. The draw band widens by `ceil(|origin|)`.
- **Pin:** `inline_run_pen_origin_chrome159_spec`: AC-1 frac 12.5547 and AC-2 whole 9.0. Both fail on base (0/2) and pass now (2/2).
- **Catalog 1x:** forms-media 3.93 -> 2.84. Each `<li><code>` line dropped from ~4.3k to ~1.8k mismatched px.
- **Not done:**
  - Wrapped runs (lines 2+ start at a line-box edge, so they are exact anyway).
  - Centred, right-aligned and RTL lines.
  - Letter- or word-spacing-adjusted runs.
  - The integer cursor itself still drifts: `<span>l</span> l` places at 10, where Chrome places at 9. The origin corrects the paint, not the box.
- **Catalog 1x, measured on base 9368a4df112 and head (rows lowered to head):**

| page | before | after |
|---|---|---|
| html | 3.51 | 2.62 |
| css-layout | 3.00 | 2.52 |
| css-paint | 3.55 | 2.80 |
| forms-media | 3.93 | 2.84 |
| animation | 3.47 | 2.91 |

  overview, evidence and tab-bar are unchanged at 1.29, 0.77 and 0.42.


## Outline (2026-11-18)
- Engine2D executor paints the outline ring in `_engine2d_draw_ir_render_outline` (`engine2d/draw_ir_adv.spl`); its raster twin is `fb_outline_clip` (`paint_primitives`). Keep them in step. Pinned by `outline_engine2d_chrome159_spec` plus the opacity spec ring points.
- Trap: a missing paint on the Engine2D lanes often means the executor ignores a Draw IR style prop the producer already emits. Grep `draw_ir_adv.spl` for the prop key before suspecting layout.


## Images (2026-11-18)
- Trap: the direct `html -> pixels` entries pass `images: []` and resolve no `data:` URLs. Resource loading is the hosted session's job. To test image paint, decode the resource and call a `*_with_images` entry (`simple_web_layout_render_html_pixels_engine2d_with_images`). "Image unpainted" through a direct entry is not a renderer bug.
- The raster (fb) lane has no image paint; only Draw IR has `_html_draw_ir_image_command`.
## 2026-11-18 — A collapsible space between inline boxes advances one face space
- **Rule:** Chrome 159 advances exactly one space of the face between two inline boxes. For Liberation Sans 16 that is 4.4453, so inline-block 120 + space puts the next box at 124.45, and the catalog button (119.48) + newline puts `<output>` at 123.94.
- **Bug:** Simple advanced 6 px:
  - a flat 5 px fallback lead space (`style_space_advance`, half the fixed cell);
  - plus a 1 px box that the `" "` node kept from a June heuristic (`space/3`, min 1). That heuristic predates the lead-space charge.
  - On forms-media this pushed "Not exercised" 2 px right.
- **Change:**
  - `resolved_space_advance` falls back to the face space (`Style.resolved_space_milli`, rounded) when the run has no interior space.
  - A collapsible whitespace-only run measures 0 once the face is known, and the inline loop zeroes its box after layout (`collapsed_space_run`), because `layout_with_style` floors a `#text` box at 1 px.
  - A run's edge spaces round together with the run: `round(width_milli + edges*space_milli)`. Rounding each piece put `, ` at 4+4 instead of Chrome's 8.89 -> 9, which drifted the overview paragraph 3 px left until this was added.
- **Pin:** `inline_space_between_elements_advance_chrome159_spec` (6 ACs). It fails on base (0/6) and passes now (6/6).
- **Matrix:** 5 button cells now match Chrome and left the baseline (154 -> 149 ids): `tt-td-button-{w,p}`, `ln-tt-td-button-{w,p}`, `tt-legend-button-p`.
- **Catalog 1x** (base b974addb1b0 -> head, both measured; rows lowered): overview 1.29 -> 1.21, html 2.62 -> 2.57, forms-media 2.84 -> 2.74, animation 2.84 -> 2.77 (row 2.91). css-layout 2.52, css-paint 2.80, evidence 0.77 and tab-bar 0.42 are unchanged.

## 2026-11-18 — `<summary>` disclosure marker: Chrome's advance and filled triangle
- **Rule (Chrome 159, list_marker.cc / list_marker_painter.cc):**
  - The disclosure symbol is a `0.66em` square, and an inside marker adds a `0.4em` end margin. Each is truncated to a LayoutUnit (1/64 px) separately, so 16 px is 675/64 + 409/64 = 16.9375.
  - The advance is identical for sans-serif, serif and monospace.
  - The symbol is a filled path in the unit square, painted with analytic AA: closed (0,0) (0.86,0.5) (0,1); open (0,0.07) (0.5,0.93) (1,0.07).
  - The square sits at the content start and ends on the baseline: top = text top + ascent − size.
- **Was:** a fixed 16 px advance (`SIMPLE_WEB_SUMMARY_MARKER_INLINE_WIDTH`, now deleted), and a `▶` / `▼` text command whose glyph Liberation Sans lacks, which painted a missing-glyph box.
- **Change:**
  - `summary_marker_symbol_64` and `summary_marker_inline_width` (layout_foundation) replace the constant.
  - The marker is a Draw IR `path` command carrying `path-fill` (ARGB) and `path-units: 64`, with its pixel bbox as the command box. Without that box, a 0x0 command paints nothing.
  - `_engine2d_draw_ir_path_fill` (draw_ir_adv) fills it with exact per-pixel area coverage: each pixel is clipped by Sutherland-Hodgman and measured by shoelace. Full spans use `draw_rect_filled` and edge pixels use `draw_rect_blend`.
  - The strict-Vulkan preflight accepts a filled path, which its fill loop clamps to the surface.
- **Pin:** `summary_disclosure_marker_chrome159_spec` (label x at 16/13 px plus closed and open triangle cells, TOL 16). It fails on base (0/3) and passes now (3/3).
- **Re-pinned toward Chrome:**
  - `details_summary_rendering_spec`: label x 16 -> 17; the marker is a `path` with exact points and box [0,3]. That spec's `-1 to equal 7` / `[0,12,0,0]` failures are pre-existing on base.
  - The paint_layout coverage-closure marker `it`.
- **Catalog 1x:** forms-media 2.74 -> 2.65.
- **Trap (narrowed 2026-11-19):** a page with no `<p>`/`<span>`/`<h1-3>`/`<button>`/`<code>`/`<label>`/`<a ` AND no bare text in the body takes the CPU raster lane (`_simple_web_engine2d_text_document`), not Draw IR. So does a bare-text page that authors `letter-spacing`, `word-spacing` or `text-shadow`. See "Bare text in a `<div>` takes the Draw IR text lane".
- **Residue:** the vertical placement uses the sans ascent (0.905em). That matches Liberation Serif at 16 px (both ascents are 14), but it is not the resolved face's ascent at every size.

## 2026-11-18 — Summary marker sits on the face baseline
- **Rule (Chrome 159):** the disclosure square ends on the summary strut's baseline. That baseline uses the resolved face's own rounded ascent and descent, with the floored half-leading above: `inline_line_strut_baseline_offset`, the same function layout uses.
- **Was:** the sans approximation, ascent 0.905em and descent 0.212em (`_html_draw_ir_chrome_text_top` + `_html_draw_ir_chrome_ascent`). It is right for Liberation Sans, but for serif 24px with `line-height: normal` (27) it gives a baseline of 22 where Chrome has 21, so the marker sat one row low.
- **Pin:** `summary_disclosure_marker_chrome159_spec` AC-4. At x=4 the closed triangle's ink spans rows 5..20 (Chrome). Base gives [6, 21] (3/4); now 4/4.
- **Residue:** at serif 24 the triangle's top edge is about 0.07 px higher than Chrome's (first-row grey 0x76 vs 0x88). The 0.66em square size has not been re-derived for that face.
- **Investigation note (forms-media 1x, not fixed):**
  - Body-text bands have 0 vertical offset (row ink centroids within 0.05 px) and matching per-glyph x.
  - The residue is per-glyph LCD coverage: Simple has about 3.5% less ink, with a +5..+8 grey bias on Chrome-coverage 1/8..1/2 pixels, plus two-signed shape noise.
  - Smaller separate classes:
    - h3 18.72px text, which is rasterised at an integer size;
    - the list disc's AA (about 14 px per bullet);
    - the inline-block control x at 92/99/91, already equal to Chrome since #10113.
## 2026-11-18 — device-px line metrics at dpr4, stage 1: text sits on Chrome's device strut baseline

- **Chrome rule (Chrome 159, `--force-device-scale-factor=4`):** line metrics are DEVICE px (zoom-for-dsf). The strut ascent and descent come from the face at size x k, each rounded on its own. Blink's subpixel-positioning borrow is on at dsf > 1 and off at 1x (hinted). It applies when the rounded descent is below the raw one and the ascent is at least 1: it moves 1 device px from ascent to descent. The half-leading is floored in device px.
  - DejaVu Sans 64 device px: 59.41 / 15.09 → 58 / 16.
  - Liberation Sans 44: 40 / 9 → 39 / 10.
  - Liberation Sans 56 and 60 take no borrow, because their descent rounds up.
- **Where k reaches layout:** `layout_device_scale_set(k)`, in `layout_foundation`.
  - It is set only by `simple_web_layout_render_html_pixels_engine2d_at_device_scale`, around layout + compose, and restored to 1 before paint.
  - The document cache key carries `;dsf=k`.
  - At k == 1 nothing is computed or recorded, and every table stays empty.
- **Strut:** `sfnt_line_metric_units_ascent_descent_device_px` (`sfnt_kern.spl`) and `browser_face_ascent_descent_device_px` (`font_renderer.spl`). k == 1 is the old milli function, with the same memo key.
- **Per-line delta:** `align_inline_line_device_dy` mirrors the baseline pass of `align_inline_line_baselines` in device px.
  - Strut items use the device strut. Atomic, bottom-edge and widget baselines use k x their CSS value, because boxes stay CSS-snapped.
  - The plain-inline recursion and sub/super are mirrored.
  - A line with a top/bottom/text-top/text-bottom box gets no correction.
  - `line delta = device ascent - k x CSS ascent`.
- **Per-text dy:** each `#text` gets `dy = line delta + (k x css ascent - round(device ascent, no borrow))`. The second term is the painter: it adds the face ascent rounded at the device size to the command top.
  - Lines 2..n of a wrapped run use the max of the line style's strut and the run's own strut.
  - Tables: `LayoutResult.device_dy` / `device_dy_rest`.
  - **Trap:** the compose rebuilds `LayoutResult` in `compose_support.spl` twice. A new per-node field must be copied there too, or it never reaches paint.
- **Wire:** the text command carries the Draw IR prop `device-y-offset` (device px). `draw_ir_composition_at_device_scale` adds it to the scaled y and strips it. It is never scaled.
- **Not moved:** text-decoration rects. The `<a href>` underline was already 2 device px above Chrome's on base (rows 60-63 vs 62-67 below the line top), so shifting it by the glyph dy would make it worse.
- **Pin:** `device_px_line_metrics_chrome159_spec`. Base 4/11, head 11/11.
  - AC-1..7 are red → green at k=4: DejaVu 16/13/12, Liberation Serif 16, Liberation Sans 11, a 24px span line, and a span with `line-height:40px`.
  - AC-8/9 are guards.
  - AC-10 holds every case at its Chrome 1x value.
  - AC-11 checks that a 4x render does not leak into a later 1x render.
- **Left for stage 2 (line-box geometry):** line-box HEIGHTS are still k x CSS px.
  - DejaVu 16px: 76 device px vs Chrome 74.
  - Liberation Sans/Serif 16px: 72 vs 74.
  - Lines and block tops therefore still drift by about 2 device px per line. Inline-block and replaced baselines are still k x CSS.
- **Residual not in this lane:** for Liberation Sans 14/15/18/20px and DejaVu 20px, the painter's own baseline sits 1 row above round(device ascent). This comes from glyph raster anchoring (the parked grayhint lane). It shows at 1x 64px Liberation Sans too: glyph ink ends at row 57 vs Chrome's 58, while the box baseline matches.
- **Catalog, stage 1 (measured 2026-11-18, blend seed, aarch64).**
  - **1x:** byte-identical code path. Every page is at its baseline row; animation is 3.40 vs its 3.52 row (noisy page).
  - **dpr4, base 9368a4df112 → head:**

    | Page | Base | Head |
    |---|---|---|
    | overview | 0.81 | 0.82 |
    | html | 2.96 | 2.87 |
    | css-layout | 4.07 | 4.02 |
    | css-paint | 4.93 | 4.87 |
    | forms-media | 5.35 | 5.27 |
    | animation | 4.16 | 4.09 / 4.06 (two runs) |
    | evidence | 0.58 | 0.57 |
    | tab-bar | 0.30 | 0.30 |

  - css-paint is still above its 4.49 row (the #9951 regression), so stage 1 alone does not close it.
  - Re-measured after rebasing onto 84ebb6ebf1b, base and head are the same numbers. The dpr4 rows lowered are html, forms-media and animation (to the worse of the two head runs). evidence (-0.01) is not a clear margin, so it is left alone.
  - The two bands that got worse are the bold h1 (overview) and the bold h3 (css-paint): their block tops are still CSS px x 4 (h1 top 66.44 CSS px lands at device row 264; Chrome puts it at 266), so the correct borrow moves the glyph 1 px further from Chrome there. Stage 2 (fractional block y and line-box height in device px) is the follow-up.

## 2026-11-18 — dpr4 snapped block top, stage 2

- **Chrome rule (dpr4):** Chrome lays out in device LayoutUnits (1/64 px) and pixel-snaps each painted edge, rounding halves up.
  - A block whose true top is 10.61 CSS px paints from round(42.44) = 42.
  - Simple's block cursor keeps y rounded to whole CSS px (`cursor_advance_px`), with the milli residual in `cy_frac`. Scaling ×4 put that block at 44.
- **Record:** `box_device_top_record`, k > 1 only, where the block cursor (or a flex row) hands a child its residual (`g_origin_frac_milli = ...`). Inline-blocks, floats, abspos and text are not recorded there, so they take their nearest recorded ancestor's top. Recording at `layout_with_style` entry instead caught inline-blocks with a reset residual 0 and moved them off their line (css-paint 4.43 vs 4.23).
  - It stores k × `g_origin_frac_milli` (milli device px) in `LayoutResult.device_top`.
  - Unset nodes hold `DEVICE_TOP_UNSET` and inherit their nearest recorded ancestor's value at paint.
  - **Trap:** a collapsed top margin re-tops a child after its layout (`corrected_top_milli`). `box_device_top_shift` moves the subtree's recorded residuals by `cy_frac - child_start_frac`, or the h2 under an h1 lands 1 px off.
- **Snap:** `box_device_top_px` first puts the residual on the 1/64 grid, then rounds halves up.
  - Simple's em margins truncate: 0.67em of 32px = 21.437, where Chrome has 21.4375.
  - Without the grid, the overview h2 at 543.496 device px rounded to 543; Chrome paints it at 544.
- **Paint:** `_html_draw_ir_device_top` (in paint_layout) post-passes `_html_draw_ir_commands` through `owner_nodes`.
  - Every command moves by its owner's snapped top. For text this adds to the stage-1 `device-y-offset`.
- **Top only, measured:**
  - Snapping bottoms from the box's END residual (`end_frac_milli`) moved the overview section's border 1 device px above Chrome (rows 1487-1490 vs 1488-1491), because Simple's container residual drifts from Chrome's.
  - With top only, a box keeps k × its CSS height. overview went 0.79 → 0.73, against 0.78 on base.
- **Pin:** `device_px_block_y_chrome159_spec`. Base 1/3, head 3/3.
  - AC-1: block rows R42-137 G224-415 R438-629 G631-726 R727-742.
  - AC-2: text baselines 111/507/603/700.
  - AC-3: guard; 1x rows stay as they are.
- **Catalog, base 4eaf71809da → head (dpr4):**

  | Page | Base | Head |
  |---|---|---|
  | overview | 0.78 | 0.73 |
  | html | 2.84 | 2.74 |
  | css-layout | 4.02 | 3.59 |
  | css-paint | 4.87 | 4.23 |
  | forms-media | 5.23 | 5.21 |
  | animation | 3.97 | 3.85 |
  | evidence | 0.57 | 0.57 |
  | tab-bar | 0.30 | 0.30 |

  - css-paint is under its 4.49 row, so the release dpr4 gate is green.
  - 1x is identical to base on every page.
- **Open:**
  - Normal line-height line boxes are still k × CSS: DejaVu 16px is 76 device px against Chrome's 74. The catalog uses `16px/1.5` everywhere, so this was not needed for the gate.
  - Fractional `height` is truncated before layout, at 1x too: `doc/08_tracking/bug/web_render_fractional_height_truncated_1x_2026-11-18.md`.
  - The Liberation Sans glyph anchoring residual is still open: h1 baseline 404 vs Chrome's 405.


- Group layers (2026-11-18): Chrome keeps an opacity-group layer premultiplied in 8 bits. Engine2D stores it straight, so its translucent-destination blend must compute the premultiplied value first (`_blend_premul_over`), then store it straight. The round trip is exact. The rule has 8 twins (C, Rust runtime, seed interpreter, oracle, scalar fallback, Metal, Vulkan GLSL+SPIR-V); change all of them together and rebuild the seed.

- Per-corner borders (2026-11-18): Engine2D paints them with `engine2d_draw_ir_render_typed_border_ring` (outer per-corner mask minus elliptical inner corners, side colour by the outer-to-inner-corner join). The corner mask samples pixel centres. The raster lane keeps its own corner AA; it is unpinned.

## 2026-11-18 — LCD low/mid coverage lift for dark text
- **Measured:** on forms-media body text (#172033), Simple's LCD mask level per channel against Chrome's, for 76.7k channel samples in rows 476..760 (tool: a per-level histogram of `round((255 - v) * 32 / (255 - L))`).
  - Chrome is one LCD16 step heavier for engine steps 2..17 of 32 and equal from about step 19 up.
  - Glyph positions and row offsets already match (see the earlier entry).
- **Change** (`lcd_s32_tables.spl`): before the colour exponent, `cov + LIFT (1 - L/255) 6.75 c^2 (END - c) / END^3` for c < END.
  - Two fitted constants: LIFT 7.5 and END 136.
  - Both are capped by Chrome-exact pins: the 16 px H stem `efbf67` has raw G 65 (< 72), and the 8 px l stem `77bfef` has raw R 133..135 (< 136).
  - Raw coverage of a pin pixel: `sfnt_render_glyph_lcd(blob, CODEPOINT, cp, size, phase)` `slg_rgb`; the bucket is `raw >> 3`.
- **Rejected shapes:**
  - The earlier exponent 0.95 for black: B 149 crosses to bucket 19 and breaks `efbf67`.
  - A parabola: it inks raw 6..7, so the device-scale 1x ink count went 186 -> 199, away from Chrome's 146.
  - An unweighted lift: light-on-dark text got worse.
- **Re-pinned toward Chrome:** in `small_text_vertical_hint_chrome159_spec`, x=4 is now Chrome's exact `CF8F5F` (was `D7975F`), and the H bar is `777777` (was `778787`; Chrome `6F7777`).
- **Hold-out** (not used to fit LIFT or END, but the `(1 - L/255)` weight was added after its white-on-dark row regressed; serif #000, serif #0f172a, sans/serif #c00000, #ddd on #101820): mismatch 2069/2252/2042/1386/1684 -> 1744/2080/1810/1248/1677.
- **Catalog 1x:**

  | page | before | after |
  |---|---|---|
  | overview | 1.21 | 1.14 |
  | html | 2.57 | 2.44 |
  | css-layout | 2.52 | 2.29 |
  | css-paint | 2.80 | 2.50 |
  | forms-media | 2.65 | 2.40 |
  | animation | 2.77 | 2.46 |
  | evidence | 0.77 | 0.68 |

## 2026-11-18 — Fractional font-size glyph raster (float x scale + float pens)
- **Was:** after #10100, layout used the float size (18.72 px), but every glyph was still rasterised at the rounded size (19 px) on the run's whole-pixel pens. `_lcd_apply_pen_phases` compared the layout's 18.72 advances with whole-19 px pens, found a mismatch, and silently returned, so the run got no quarter phases at all.
- **Measured** (Liberation Sans, `line-height:normal`, 320x40, mismatched px > 8 / summed |delta|):

  | page | base | pens only | x scale only | both | whole-px reference |
  |---|---|---|---|---|---|
  | sans 18.72 | 1264 / 158k | 1066 / 99k | 933 / 130k | 725 / 70k | 19 px: 379 |
  | sans 13.28 | 666 / 74k | 535 / 33k | 532 / 71k | 309 / 28k | 13 px: 209 |
  | serif 18.72 | 1235 / 140k | 1048 / 100k | 1197 / 130k | 814 / 78k | |
  | serif 13.28 | 687 / 84k | 514 / 37k | 653 / 82k | 369 / 34k | |
  | sans 10.72 | 567 / 65k | 438 / 31k | 506 / 54k | 252 / 20k | |

  - Pens contribute most of the summed delta; the x scale contributes the most mismatched px at 18.72, because each 19 px glyph is 1.5 % too wide. Neither alone is enough.
  - **Vertical hinting contributes nothing.** Chrome's 18.72 px rows equal its 19 px rows, and its 13.28 rows equal its 13 rows. FreeType's light autohinter fits the y scale to the whole-pixel x-height. The 18.72 residual after the fix has the same row shape as the whole-19 px residual.
- **Change:**
  - The producer emits `font-size-milli` on the text command only when the size is fractional. `draw_ir_device_scale` scales it by k.
  - `draw_ir_adv` → `Engine2D.draw_text_with_advances(..., size_milli)` (and the `_vulkan_only` twin) → `stage_text_with_advances_configured` → `_lcd_apply_pen_phases`.
  - **Exact pens:** the paint side rebuilds the layout's model (`resolve_font_metrics_with_language_milli`). It takes exact milli pens at ref = 8 x round(size), capped at 512, and rescales them to `size_milli`. Whole-pixel boundaries use `round(round(ref_pen) * milli / ref)`. On the 18.72 probe the advances match the layout's exactly. A mismatch keeps the float outline at phase 0.
  - **Raster:** every glyph of a fractional run is swapped for a cell from `sfnt_render_glyph_lcd_milli`. The outline x is scaled by `milli / (size_px * 1000)`. y, the hint knots and the hint cache stay at the whole `size_px`, so the "13.5 rounds down for rows" pin holds.
  - Cells are keyed `glyph_index = -1 - phase - 4 * size_milli`, and `_lcd_phase_glyphs` includes `x_milli`.
  - Whole-px runs carry no prop and take the old code path byte for byte.
- **Pin:** `fractional_glyph_raster_chrome159_spec` (18.72 and 13.28, four Chrome windows). Red 0/2 on base, green 2/2.
- **Catalog 1x** (base and head measured on the same seed; rows lowered to head):

  | page | base | head |
  |---|---|---|
  | html | 2.44 | 2.35 |
  | css-layout | 2.29 | 2.22 |
  | css-paint | 2.50 | 2.43 |
  | forms-media | 2.40 | 2.33 |
  | animation | 2.39-2.46 | 2.33-2.40 (paired re-runs 2.46 -> 2.33 twice) |
- **Catalog dpr4:** identical on all 8 pages, base and head (css-paint 4.87 against its 4.49 row is red on base, from the strut lane). No catalog page has a fractional LCD run at dpr4.
- **Perf** (css-paint 1x, same seed): base 54.5 / 53.2 s, head 55.8 / 52.6 s; RSS 774-791 MB on both.
- **Not done / found:**
  - Grayscale glyphs (device size > 48 px, i.e. 18.72 and 13.28 at dpr4) still rasterise at the whole device size.
  - At dpr4 the layout advances are k x CSS advances, which never equal the device-size model. A fractional LCD run (10.72 x 4) therefore takes the float outline at phase 0.
  - **Serif bold is not bold** (separate bug, face resolution): `font-family:serif;font-weight:bold`, including the UA serif `<h3>`, paints Liberation Serif Regular on both the LCD and gray paths, even at 19 px. That is 1839 mismatched px per line against Chrome, which dwarfs the fractional effect on serif h3 lines. Sans bold is fine.
  - **`line-height:1` at a fractional size** puts the baseline one row low. Blink floors the half-leading (-1.14 → -2), and Simple does not. That belongs to the line-box lane.


## 2026-11-18 — Bold serif paints Liberation Serif Bold (Chrome 159)

- **Was:** `browser_font_family_for_weight` (`src/lib/nogc_sync_mut/text_layout/font_provider.spl`) routed bold only for the sans and mono generic families. A serif family, and the default serif face (no name served, #10089), kept the regular face. Every UA heading and `<b>` on a serif page painted Liberation Serif Regular, on both the LCD path and the grayscale path above 48 device px. The `<b>` band was byte-identical to the regular `<span>` band.
- **Chrome 159** (fontconfig `serif:bold` -> LiberationSerif-Bold.ttf): `<b>Hamburgefonstiv</b>` at 16px is 120.00 px wide; the regular face is 111.69 and the UA h3 at 18.72px is 140.28.
- **Fix:** `browser_platform_serif_bold_faces()` (Liberation Serif Bold, only when Liberation Serif Regular is also present, so it is never a typeface swap). Routed for `category == "serif"` and for an unserved list whose default is serif. `web_font_face_candidates` goes through the same router, so the grayscale path is fixed too.
- **Measured** (320x100, dark = 765 - (r+g+b), mismatched px = dark delta > 24 against Chrome): h3 1297 -> 359, `<b>` 1022 -> 249. Ink extent h3 0..130 -> 0..139 (Chrome 0..140), `<b>` 0..111 -> 0..119 (Chrome 0..119). 60px bold `H` stem row dark 4398 -> 7074 (Chrome 7050).
- **Byte-identical** base vs head: sans regular/bold/italic/bold-italic, mono bold, regular serif, serif italic.
- **Spec:** `test/01_unit/browser_engine/serif_bold_face_chrome159_spec.spl`, base 1/4 -> head 4/4.
- **Catalog:** every catalog page declares `font: 16px/1.5 sans-serif`, so 1x and dpr4 are unchanged . 1x head equals every row (overview 1.14, html 2.35, css-layout 2.22, css-paint 2.43, forms-media 2.33, animation 2.40, evidence 0.68, tab-bar 0.42). dpr4 base/head: overview 0.78/0.78, html 2.84/2.84, css-layout 4.02/4.02, css-paint 4.87/4.87 (red against the 4.49 row on base too, from #9951), forms-media 5.23/5.23, animation 3.94/3.97 (all-sans page, capture-timing noise), evidence 0.57/0.57, tab-bar 0.30/0.30. No row changed. Perf on a bold-serif page (2 runs each): base 5.9/4.9 s and 685/691 MB, head 6.0/5.0 s and 684/691 MB.
- **Follow-up landed:** serif italic and bold-italic are routed by the next entry (Liberation Serif Italic / BoldItalic).
- **Trap:** the pure-Simple PNG decoder rejects Chrome's `--screenshot` stream and this host has no `magick`. Decode it in Chrome itself: load the PNG into an `<img>` on a `file://` page, `drawImage` it onto a canvas, and dump `getImageData` as P3 text through `--dump-dom --allow-file-access-from-files`.

## 2026-11-18 — Italic serif paints Liberation Serif Italic / BoldItalic (Chrome 159)

- **Was:** `browser_font_family_for_style` (`src/lib/nogc_sync_mut/text_layout/font_provider.spl`) routed italic only for the sans and mono generic families. `<i>`/`<em>` in a serif family, or in the default serif face when no listed family is served, painted Liberation Serif Regular upright (the `<i>` band was byte-identical to the regular band), and `<b><i>` painted upright Bold.
- **Chrome 159** (LiberationSerif-Italic.ttf / LiberationSerif-BoldItalic.ttf): `<i>Hamburgefonstiv</i>` at 16px is 110.52 px wide and `<b><i>` 115.56, for the default family, `font-family: serif`, `'Times New Roman'` and an unserved name alike; upright regular 111.69, upright bold 120.00.
- **Fix:** `browser_platform_serif_italic_faces()` and `browser_platform_serif_bold_italic_faces()`, each only when Liberation Serif Regular is also present (never a typeface swap), routed for `category == "serif"` and for the unserved default-serif case, the same condition the serif bold route uses. Linux paths only; no macOS face is guessed. A host without the italic file keeps the weight-only routing.
- **Measured** (320x100, dark = 765 - (r+g+b), mismatched px = dark delta > 24 against Chrome): `<i>` 772 -> 244, `<b><i>` 1002 -> 218, regular 238 -> 238. Ink extent `<i>` 0..111 -> 0..110 (Chrome 0..110), `<b><i>` 0..119 -> 0..115 (Chrome 0..115). 60px `l` stem left edge near top / bottom: `<i>` 26/26 -> 29/24 (Chrome 30/24), `<b><i>` 124/124 -> 128/122 (Chrome 128/122).
- **Byte-identical** base vs head: sans and mono regular/bold/italic/bold-italic, serif regular/bold/UA h3, and the serif bold spec page.
- **Spec:** `test/01_unit/browser_engine/serif_italic_face_chrome159_spec.spl`, base 1/4 -> head 4/4.
- **Catalog:** every catalog page declares `font: 16px/1.5 sans-serif`, so no row moved. 1x head equals every row (overview 1.14, html 2.35, css-layout 2.22, css-paint 2.43, forms-media 2.33, animation 2.40, evidence 0.68, tab-bar 0.42). dpr4 head/base: overview 0.73/0.73, html 2.74/2.74, css-layout 3.59/3.59, css-paint 4.23/4.23, forms-media 5.21/5.21, animation 3.85/3.82 (all-sans page, capture-timing noise as in the serif bold entry), evidence 0.57/0.57, tab-bar 0.30/0.30.
- **Perf** (3 runs each, same seed): pages without serif italic are unchanged (sans 7.12 -> 7.14 s, mono 7.16 -> 7.13 s, serif regular/bold 5.90 -> 5.89 s; RSS 685..693 MB both sides). The italic spec page goes 4.83/4.91/4.94 s -> 5.75/5.75/5.77 s at the same 686 MB: it now loads three faces (Regular, Italic, BoldItalic) where base loaded two (Regular, Bold), and each extra face load costs about 0.9 s in the interpreter (the three-face serif bold page is 5.85 s on both sides).
- **Not pinned:** the 60px serif ink box sits two rows higher than Chrome's (rows 11..52 against 13..53) for the upright face too; this is vertical placement, not the face.

## 2026-11-18 — Negative and fractional leading: every inline box floors its half-leading (Chrome 159)

- **Chrome rule (measured, Liberation Sans/Serif, 10 sizes x 5 unitless line-heights):** ascent and descent are rounded to whole px at the float size. The half-leading `(line-height - (ascent + descent)) / 2` is FLOORED for the strut AND for each inline box. A content area taller than the line-height overflows the line; it does not grow it.
  - `16px/1` (14/3): span top -1, baseline 13, div 16.
  - `18.72px/1` (17/4): -1.14 -> -2, baseline 15.
- **Was (three defects, one symptom: text one row off at 1x):**
  - The text run's own half-leading (`text_half_leading` in `align_inline_line_baselines`) used `/ 2`, which truncates toward zero. An odd negative leading lost a row: `16px/1` baseline 14, `22.4px/1` 19 (Chrome 13 / 18). The strut already floored.
  - A one-line inline element gave the line its content area (`layout_engine`, inline branch). A `16px/1` div with a `<span>` was 17 px, a `19px/1` one 21 (Chrome 16 / 19).
  - The `font:` shorthand dropped the size fraction (`font_size_milli_v = 0`). `font:15.5px/1.5` was 15 px with a 22 px line (Chrome 23.25); `17.6px` was 17 px. The `font-size` longhand kept it.
- **Fix:** `_floor_div_i32` for the run's half-leading. The inline branch keeps the pre-swap box height as the line contribution when the content area is taller. `parse_font_shorthand_size_milli` (replaces `parse_font_shorthand_size_px`) feeds `font_milli_round_px` / `font_milli_store`.
- **Pin:** `line_height_one_half_leading_chrome159_spec`, base 1/7, head 7/7.

  | probe (Chrome-equal cases) | base | head |
  |---|---|---|
  | geometry, `font:` shorthand (b top, span top, span height) | 46 / 99 | 99 / 99 |
  | geometry, longhands | 81 / 99 | 99 / 99 |
  | 1x glyph baseline, 50 cells | 35 / 50 | 50 / 50 |
  | dpr4 glyph baseline, worst cell | 5 rows | 3 rows |

- **Catalog:** 1x and dpr4 equal every baseline row on all 8 pages (the pages use `font: 16px/1.5`: positive leading, whole size), so no row moved. dpr4 animation read 3.82 on base and 3.85 on head, one run each (3.85 is its row; earlier lanes recorded the page as noisy). Matrix unchanged at 85 mismatching cells.
- **Perf** (css-paint 1x): base 51.29 / 51.28 s, head 50.52 / 50.84 s; max RSS 795-797 MB on both.
- **Found, not landed (dpr4 fractional size):** `draw_ir_device_scale` scales `font-size` as round(css) x k, so 14.4 px paints at 56 device px and 15.5 at 60 (Chrome 57.6 / 62). Scaling from `font-size-milli` (and reading the painter ascent at that size in `text_device_painter_dy`) makes 20 of the 50 dpr4 cells exact and leaves the other 30 one row high, but the dpr4 catalog got worse on two pages: html 2.74 -> 2.76, forms-media 5.21 -> 5.23. On a UA-size probe the h5 and h6 bands improved (3193 -> 2759, 3069 -> 2827 mismatched px) and the sub/sup band got worse (3481 -> 3702). Two older dpr4 offsets sit under it: `<small>` in a 16px/1.5 line is 5 device rows above Chrome, and `<sub>` 3 rows below. Fix those first.
- **Consequence at dpr4:** a `font:` shorthand with a fractional size now behaves like the longhand. For 14.4 and 15.5 px that is one device row further from Chrome than the truncated 14 / 15 px was (2 -> 3 rows high at worst). No cell of the other eight sizes is further, and 16, 17.6, 18.72, 22.4 and 10.72 px are up to 5 rows closer.
- **Still open:** line heights are whole px (`17.6px/1` is 17, Chrome 17.59).
- **Trap:** the export lists of the `simple_web_html_layout_renderer*` modules name every function on one line. Renaming a function means editing nine of them, and any other lane that adds an export conflicts.
- **Trap:** a probe script outside the repo cannot import `common.*` or `std.*`; put it under the worktree, untracked, and move it out before committing. `simple run` on a file under `examples/` stops after 10 s unless `SIMPLE_TIMEOUT_SECONDS=0` is set; the output looks like a fast run.
- **Trap:** `decode_png_to_argb` did decode Chrome's `--screenshot` PNGs here, so a probe can read both sides in one `.spl`.

## 2026-11-18 — "Per-face" load cost is per cold GLYPH: 1.03 s -> 0.68 s per 15-glyph face, byte-identical

- **Reframe:** #10208 read the +0.9 s of a third serif face as a face-load cost. Loading is 2..3 ms (`file_read_bytes` 2 ms, `font_runtime_ttf_default_supported` 1 ms, `try_load_runtime_ttf` 2 ms). The cost is the first raster of each (face, size, glyph): a page with ONE face goes 2.76 s for 1 glyph, 3.65 s for 15, 4.57 s for 30, and a second size of the same 15 costs the same +1.1 s. A new face only brings 15 cold glyphs with it.
- **Breakdown** (interpreter lane, the catalog's `SIMPLE_EXECUTION_MODE=interpreter`, 15 glyphs at 16px, of 1050 ms): LCD raster `sfnt_render_glyph_lcd_milli` 503 ms in 26 calls (15 at phase 0, 11 quarter-phase cells; inside: edges 165, row scan + FIR 199, cmap/table setup 58, hint 63); grayscale `sfnt_render_glyph_into` 198 ms whose pixels the LCD glyph then replaces; measure 77 ms and `has_glyph` 62 ms, each a full cmap re-parse; about 200 ms outside the glyph path. The interpreter runs about 1 us per basic op, so op count is the lever, not table size.
- **Fixes** (all in `src/lib`, no rendered byte moves):
  - `_selected_outline_gid` (`font_renderer.spl`): the cold glyph path takes the glyph id from the per-face ASCII table (`_gid_warm`, one cmap parse per face) for `has_glyph`, the measure pass and the phased LCD cell. Guarded by `FontRasterizer.has_glyph_reads_selected_blob()` so a foreign provider still answers its own `has_glyph`.
  - LCD first: an LCD-size glyph kept only two receipts of the grayscale render, the advance (already in the measure meta) and "has ink" (`meta[9] > 0`). `sfnt_glyph_gray_row_has_ink` (`sfnt_glyf.spl`) proves the second from the middle pixel row through the same kernel on the same coordinates (`_outline_edges_band`, `_glyf_raster_alpha_rows`). No proof (`:`/`=` have an empty middle row) or no LCD glyph runs the old path unchanged.
  - `_add_edge` no longer aliases its array (`var result = edges` made each push copy: 500 pushes 6.8 ms against 3.3 ms, quadratic beyond, on the JIT too) and `_quad_edges` emits the last split's two chords itself (31 -> 15 calls per curve, same points).
  - `_edge_row_index`: both scanline kernels read only the edges that can reach the pixel row (a superset filter; the exact test and the edge order are kept). Neutral at 16px, it is what makes a one-row raster cheap.
- **Trap:** shifting the outline to raster one row as "row 0" is NOT the same floats (`(-y*s) - (top + r)` against `((-y*s) - top) - r`); the row proof must keep the render's coordinates and select rows in the kernel.
- **Perf** (seed 60799992 bytes 2026-11-17 16:01, 3 runs, median wall; RSS 687..692 MB both sides): serif page with 0/1/2/3/4 faces base 2.58/3.65/4.65/5.71/6.71 s, head 2.61/3.32/4.00/4.59/5.34 s. Sans 4 faces 7.06 -> 5.32 s, mono 7.20 -> 5.53 s, a 10-size 1..18.72px page 24.8 -> 17.4 s.
- **Byte-identical** base vs head (`cmp` of the PPMs): serif 0..4 faces, sans and mono all four styles, 30 glyphs, two sizes, sizes 1..18.72px incl. fractional, 24/40/49/60px, and the JIT/Vulkan lane.
- **Spec:** `test/01_unit/lib/common/encoding/sfnt_glyf_public_api_spec.spl`, 2 new cases (the row proof is never true for a bitmap the render leaves empty, over ASCII at 1/3/16px; input rejection). Base 10/10 with the two absent, head 12/12.
- **Catalog** (900x760, one run each, PPMs identical on all eight): overview 21.7 -> 18.9 s, html 44.4 -> 42.5, css-layout 47.3 -> 44.9, css-paint 52.4 -> 48.6, forms-media 42.3 -> 39.3, animation 42.5 -> 40.0, evidence 13.3 -> 12.2, tab-bar 6.2 -> 5.5. Glyph raster is 5..13% of a catalog page; the rest is layout and paint.
- **Left on the table:** the phase-0 LCD cell of a glyph that is then drawn from a quarter-phase cell (11 of 26 LCD rasters here, about 200 ms per face) and the LCD raster itself (about 12 ms per glyph).

## 2026-11-18 — Large text sits on Chrome's baseline row (grayscale frame, blockified inline half-leading)
- **Measured (Chrome 159, `H`, Liberation Serif / Sans, ink rows with dark > 380):** the 60px serif glyph of #10208 was two rows high for two separate reasons, one row each.
- **Cause 1, layout** (`align_inline_line_baselines`, `simple_web_html_layout_renderer_layout_foundation.spl`): a text run takes its own floored half-leading only when the line owner is not `display:inline`. A floated or absolutely positioned `<span>` is blockified (CSS 2.2 9.7) but its `display` still reads `inline`, so the run got none. One row at `line-height: normal` wherever the rounded line gap is 2 px or more (serif from 40px, sans from 48px), and the WHOLE half-leading with an authored line-height: abs span `16px/40px` painted rows 13..23 (Chrome 24..34), `48px/1` 21..52 (Chrome 18..49). Fix: the condition also accepts `float_mode != 0`, `position_absolute`, `position_fixed`.
- **Cause 2, raster** (`_gray_frame`, `src/lib/common/encoding/sfnt_glyf.spl`): the grayscale bitmap (device size above 48 px: every dpr4 glyph, 1x from 49px) hung from its own ink top with `height = ceil(ink height)` and `bearing_y = round(min y)`, so the ink bottom floated up to one row above the baseline, by a different fraction per glyph. Chrome keeps the outline unhinted there but counts rows from the baseline (96 device px serif `H`: bottom row solid 765, top row partial 561; ours was 573 bottom / 765 top). Now `bottom = floor(min y)`, `top = ceil(max y)`, `bearing_y = bottom`, shared by `sfnt_measure_glyph_into`, `sfnt_render_glyph_into` and `sfnt_glyph_gray_row_has_ink`. Below 49 px the old frame stays (Chrome paints LCD there; that raster is unmeasured for other consumers).
- **Rows, abs span at top 0, Chrome / base / head:** serif 40px 11..36 / 10..35 / 11..36; 48px 12..43 / 11..42 / 12..43; 60px 15..53 / 13..51 / 15..53; 72px 18..64 / 16..62 / 18..64. Sans 48px 11..43 / 10..42 / 11..43; 60px 14..54 / 12..52 / 14..54; 72px 16..65 / 15..64 / 16..65. dpr4 UA `<h1>` sans 115..202 / 114..201 / 115..202. UA `<h1>`/`<h2>` at 1x already matched (29..49, 86..100).
- **Spec:** `test/01_unit/browser_engine/large_text_vertical_placement_chrome159_spec.spl` (4 cases, 0/3 on base before AC-4 existed, 4/4 now).
- **Re-pin (engine value, toward Chrome):** `web_device_scale_spec` 4x `Hg` ink 1629 -> 1625 (Chrome 1640). Per-pixel mismatch against Chrome 664 -> 445 of 15,360, summed channel difference 191,742 -> 75,900.
- **Catalog:** 1x css-layout 2.22 -> 2.19 (row lowered), others equal. dpr4 base/head: overview 0.73/0.65, html 2.74/2.60, css-layout 3.59/3.42, css-paint 4.23/4.06, forms-media 5.21/5.16, animation 3.85/3.81 (row kept), evidence 0.57/0.50, tab-bar 0.30/0.30; six rows lowered.
- **Residual:** at 1x above 48px Chrome still hints the grayscale outline (cap top on a whole row, edges 765/765); ours keeps a partial top row (serif 60px row 14 at 25%, sans 49px row 11 at 75% where Chrome starts at 12). `g` at 60px sans: Chrome 24..66, head 23..67, base 21..65. That needs the blue-zone knots on the gray raster at dpr 1 only, and the raster does not know the dpr. At dpr4, block tops below the first line still drift (CSS-snapped line heights, the device-px line lane).
- **Trap:** `git worktree add` for a base run costs 2.8 GB. With the change committed, `git checkout origin/release/1.0.0 -- <changed src files>` in the lane worktree gives the same base, and `git checkout HEAD -- <files>` restores it.

## 2026-11-19 — LCD cold glyph: undrawn phase-0 cells deferred, raster reads only the edges a sample crosses (byte-identical)

- **Why the phase-0 cell was built at all:** `stage_text_with_advances_configured` reads every glyph of a run through `get_glyph` before the pens are known (`_glyph_pen_advances`, then three loops in `_stage_text_active`), and `get_glyph` only knew how to answer with a rastered cell, which the quad loop then put into the atlas. `_lcd_apply_pen_phases` runs last and swaps every quad whose exact pen rounds to quarter 1..3 (and every quad of a fractional-size run) for a phase cell. For such a glyph the pass had read the phase-0 cell's metrics only (advance, width, height, bearings); its pixels and its atlas cell were never drawn.
- **Fix 1, deferral** (`font_renderer.spl`): while that one pass runs (`lcd_defer_cells`), a cold LCD glyph is answered with its metrics alone, `CachedGlyph.lcd_frame_only` (`_lcd_frame_glyph`, from `sfnt_lcd_outline_frame`: same width, height and bearings as the raster, no pixels). Its quad is staged with `atlas_x = -1`. `_lcd_apply_pen_phases` swaps in the phase cell as before; `_lcd_resolve_deferred_cells` then rasters only the cells still drawn at phase 0 and names them in the dirty rects (`_lcd_publish_cells`, the block the phase cells already used). `get_glyph` outside the pass never returns a frame: a cached frame is filled in place first (`GlyphCache.fill_frame`). An atlas that cannot take a deferred cell is reset and the run staged again with every cell up front.
- **Fix 2, one outline per glyph** (`sfnt_glyf.spl`): `sfnt_render_glyph_lcd_milli` is now `sfnt_lcd_glyph_outline` (parse, x scale, hint, vertical frame, advance: nothing the phase touches) followed by `sfnt_lcd_outline_raster(outline, phase)`. The renderer keeps the outline per (face, glyph, size, x milli) in `_lcd_outlines`, so the second to fourth phase of a glyph, and the fill of a deferred cell, skip the parse and the hint.
- **Fix 3, the raster** (`sfnt_glyf.spl`). `sfnt_render_glyph_lcd_milli` at 16px by glyph index: 14.8 -> 10.8 ms per call; the raster alone, on a cached outline, is 8.0 ms.
  - `_lcd_outline_edges` leaves out the chords no sample scanline crosses. A curve is always 16 chords, and the kernel reads an edge only at sy = (2t + 1) / 8: 76% of the edges of a 12px glyph, 71% at 16px, 63% at 24px and 49% at 40px lay between two scanlines, built and indexed for nothing. A whole sub-curve is skipped when the y range of its three control points holds no scanline.
  - `_edge_sample_index` indexes edges by sample scanline instead of by pixel row (`_edge_row_index` made the kernel test each of a row's edges four times).
  - `_lcd_accumulate_row` takes its crossing scratch from the caller, and reports the subpixel span it wrote; the FIR and the gray plane are computed over that span plus the filter's reach only. The rest of the row is the 0 it was allocated as.
- **Trap, and a bug filed:** a deferral that keeps its frames OUT of the renderer's `GlyphCache` changes pixels on any page with more than 8 (face, size) pairs. `get_glyph_advance_milli` refills an evicted advance slot from the glyph cache with `advance * 1000`, a whole pixel, so which glyphs are in that cache decides the pens (and whether a run gets quarter phases at all). The first draft rendered sizes 1..15 in four faces differently on the 1, 4, 8, 12 and 15px lines. The frames are therefore inserted into the glyph cache at the moment base inserted the rastered glyph, and filled in place. `doc/08_tracking/bug/glyph_advance_refilled_whole_px_from_glyph_cache_2026-11-19.md`.
- **Trap:** `_lcd_resolve_deferred_cells` and the fill path must not rescan. `_font_atlas_entry_index` and the cross-instance raster-key scan are linear in everything rastered so far; one extra scan per resolved quad made the 120-pair page slower than base (110.9 -> 123.9 s user; 109.9 -> 108.7 after) until the resolve pass kept its own codepoint list and the fill skipped the key scan.
- **Trap:** edges cannot be shared between phases. The phase enters as `x * scale - (x0 - phase / 4)` before the midpoint splits, so a translated edge list is not the same floats; only y, the direction and the sample index are phase-free. Not done.
- **Cold glyph now** (16px, interpreter lane, per glyph): measure 1.7 ms, ink row proof 2.7, outline 2.7, raster 8.0. Base was 1.7 + 2.7 + 14.8, plus another 14.8 for a phased glyph.
- **Perf** (seed 60799992 bytes 2026-11-17 16:01, interpreter lane, 3 interleaved runs, median wall, load 3.6; RSS 688..712 MB both sides): serif page with 0/1/2/3/4 faces base 2.57/3.28/3.96/4.69/5.31 s, head 2.58/3.11/3.52/3.97/4.44 s, so 0.69 -> 0.47 s per 15-glyph face. Sans 4 faces 5.44 -> 4.53 s, mono 5.47 -> 4.51 s. Seven fractional sizes in four faces (every glyph phased) 35.3 -> 24.2 s. Sizes 1..15 in four faces 41.5 -> 37.9 s: with 60 (face, size) pairs the advance quirk above puts nearly every glyph on phase 0, so only the raster gain is left.
- **Catalog** (900x760, base and head run side by side, user s): overview 18.7 -> 17.4, html 41.0 -> 40.0, css-layout 43.7 -> 42.2, css-paint 48.8 -> 47.5, forms-media 38.9 -> 37.6, animation 39.6 -> 38.5, evidence 11.7 -> 11.2, tab-bar 5.0 -> 4.7. About 3%: glyph raster is a small part of a catalog page, and those pages are past 8 (face, size) pairs. At dpr4 the pairs differ by less than the run-to-run noise.
- **Byte-identical** base vs head (`cmp` of the PPMs): serif 0..4 faces, sans and mono four faces, 30 glyphs, two sizes, 24/40/49/60px; serif, sans and mono in all four styles at every size 1..60px, at 1..15px with dpr4, and at seven fractional sizes; all eight catalog pages at 1x and dpr4; the JIT + Vulkan lane (three families, fractional page). Raster level, `sfnt_render_glyph_lcd_milli` hashed over ASCII 33..126 x 4 phases: Liberation Serif at every size 1..60 (22,560 cells), Sans, Sans Bold, Mono, Serif Italic and Mono Bold Italic at 29 sizes 1..60 (10,904 each), all six at seven sizes with a .72 fractional x scale.
- **Spec:** `advance_staging_pen_drift_spec.spl` AC-4..6 (the atlas holds only the cells the run draws: base 24 cells for 15 drawn, head 15; a deferred run equals an eagerly rastered one cell for cell; a glyph read afterwards has its pixels) and `sfnt_glyf_public_api_spec.spl` (the outline frame is the raster's metrics at every phase). Base 4/6, head 6/6 and 13/13.
- **Left on the table:** the measure pass, the ink proof and the outline each parse the table directory and the glyph (three parses, about 2.5 ms of the 15 ms cold glyph). `cache.lookup`, `_font_atlas_entry_index` and the raster-key scan are linear and run per glyph per run; on the 60-pair page staging is 21 s of 40 s.

## Images

- Raster (software) lane paints `<img>` only via `simple_web_layout_render_html_software_pixels_with_images(html, w, h, images)`; the plain entries paint none. The painter (`_fb_paint_img_clip`, paint_raster) runs in document order right after the node's box paint, with Draw IR geometry via the shared `html_image_fit_size`. Nearest-neighbour is exact only for uniform images (`# ponytail:`); overlapping-paint opacity cells (`tg_page` (50,12)) stay un-admitted on the raster. Spec: `test/01_unit/browser_engine/img_raster_chrome159_spec.spl`.

- Raster per-corner borders (2026-11-18): differing radii + solid sides go through `fb_border_ring_per_corner_clip` (pixel-centre outer mask minus elliptical inner corners, same model as Engine2D `typed_border_ring`); uniform radii keep the AA arc painter. Pinned by `border_per_corner_radius_chrome159_spec`.

- Outline phase (2026-11-18): in-flow outlines paint after their context's in-flow members, before positioned children (raster: after pass 1; Draw IR: `<id>#outline` twin flushed at the context boundary).

## 2026-11-18 — atomic inline `vertical-align: middle` centres the margin box on baseline + x-height/2

- **Was:** a `middle` inline-block / `<img>` / form control never entered `align_inline_line_baselines`: it stayed at the line top (y=0) for every margin and the line only grew to its border box. `<img>` and `<input>` (which this engine carries as `display:inline`) also missed the margin-box path for `top | bottom | text-top | text-bottom`, because `inline_atomic_valign` rejected every `display:inline` box.
- **Rule (Blink):** with X = `LayoutUnit::FromFloatRound(x-height / 2)` (1/64 px) and M the margin-box height, the margin box spans `[baseline - X - M/2, baseline - X + M/2]`; the line's ascent / descent are the max of the strut and those two reaches. x-height is Skia's: OS/2 `sxHeight` (Liberation Sans 1082/2048, Liberation Serif 940/2048), 0.56 x ascent for a face without one.
- **Fix:** `sfnt_blob_x_height_units` (`sfnt_kern.spl`) reads `[sxHeight, upem]`; `browser_face_x_height_units` (`font_provider.spl`) resolves the style's face with the same candidate walk as ascent/descent and memoises per face file; `inline_middle_half_x_height_64` + the `middle` branches in `align_inline_line_baselines` (`simple_web_html_layout_renderer_layout_foundation.spl`) keep the reach in 1/64 px, snap the box top half up (the row Chrome paints on) and the line height to the rounded sum. `inline_atomic_valign` now treats a replaced element / form control as atomic whatever its `display`.
- **Chrome 159 vs base vs head** (y of a 20x10 box after "x", div height): 16px Liberation Sans no margin 4.766,18 / 0,18 / 5,18; `margin-top:6px` 7.766,18 / 0,18 / 8,18; `margin:5px 0` 5,20 / 0,18 / 5,20; 16px serif `margin:5px 0` 5.328,20.328 / 0,18 / 5,20; 24px Liberation Sans no margin 10.656,28 / 0,28 / 11,28; `<input>` 24px 5.156,28 / 0,28 / 5,28. Full matrix (5 keywords x 3 fonts x {inline-block 10/40 px, img, input} x 8 margins = 480 cells, rounded half up): base 260 wrong, head 0 wrong. Painted rows at 1x equal Chrome's (5..14, 8..17, 5..14, 11..20).
- **Spec:** `vertical_align_middle_margin_chrome159_spec` (10 cases, 0/10 on base, 10/10 now).
- **Residual:** boxes stay CSS-snapped at device scale > 1, and Chrome lays out in device px there (64 px face: baseline 59, not 4 x 14). dpr4 painted top in device px, Chrome / head (base lays every one out at y=0): 16px Sans 22 / 20, `margin-top:6px` 34 / 32, 24px Sans 42 / 44, serif `margin:5px 0` 23 / 20. A line's fractional height (20.328) is rounded, so the block below can sit up to half a px off. `middle` on a plain `display:inline` element (a span) is still unhandled.

## 2026-11-18 — grid item margins resolve against, and fill, the grid AREA

- **Rule (CSS Grid 6.1 / 11.1, Chrome 159):** a grid item's containing block is its grid area. Percent margins on ALL four sides are of the area's inline size (the spanned tracks plus the gaps between them), never the grid container's width. An auto-width item's margin box fills the area (`x += margin-left`, `w = area - margin-left - margin-right`); a specified width (px or percent) still resolves against the whole area. Vertical margins are part of an implicit row's size.
- **Was (wider than percent):** the grid loop in `layout_with_style_flow` (`..._layout_engine.spl`) read `margin_t` / `margin_b` as whole px (`10%` = 10 px, the pre-#10039 legacy value), ignored horizontal item margins entirely (px too) and sized implicit rows from the border box, so every item margin ran into the next row.
- **Fix:** `grid_child_width` (the area) is computed first; `grid_margin_l/r` = `resolve_horizontal_margin_px(.., area)` (auto = 0 as before), `grid_margin_t/b` = `vertical_margin_px_in(.., area)`; x and the auto width use them; an implicit row grows to `height + margin_t + margin_b`; the child style goes through `style_with_resolved_percent_margins(.., area, ..)` so no reader sees the negative milli.
- **Chrome 159 / base / head** (x y w h relative to a 400 px grid): `100px 300px` + `margin:10%` item 1 10 10 80 20 / 0 10 100 20 / =Chrome, item 2 130 30 240 20 / 100 10 300 20 / =Chrome, grid h 80 / 20 / 80; `1fr 3fr` `margin:25%` 175 75 150 10 / 100 25 300 10 / =Chrome; `1 / span 2` over a 20 px gap `margin:10%` 22 22 176 10 / 0 10 220 10 / =Chrome; `width:50%;margin-left:10%` in the 300 px track 130 0 150 10 / 100 0 150 10 / =Chrome; explicit 60 px row, 200 px track, `margin:10%` stretched 20 20 160 20 / 0 10 200 40 / =Chrome; px `margin:11px` 11 11 78 20 / 0 11 100 20 / =Chrome.
- **Trap — a percent `width` must NOT see the margin-reduced width.** `layout_with_style` resolves a percent width against the available width it is passed, so only an auto-width item gets `area - margins`.
- **Still open** (`doc/08_tracking/bug/web_percent_padding_unparsed_and_grid_bare_span_2026-11-18.md`): percent PADDING is not parsed anywhere (`_padding_length_px` rejects `%`, the declaration is dropped), so grid-area padding cannot be compared yet; a bare `grid-column:span N` normalizes to "" (`1 / span N` works); `normal` stretch only happens in explicit rows; auto inline margins and `justify-self` do not shrink-to-fit.
- **Spec:** `test/01_unit/browser_engine/grid_item_percent_margin_chrome159_spec.spl` (7 cases, 0/7 on base, 7/7 now).
- **Gates (blend seed):** catalog 1x base = head = rows on all 8 pages (1.14 / 2.35 / 2.19 / 2.43 / 2.33 / 2.40 / 0.68 / 0.42); dpr4 base = head = rows on 7 pages, animation 3.81 base vs 3.78 head (row 3.85 left alone, the page is time-sampled). No catalog page has a grid item with a margin, so no row moved. Matrix PASS (979 cells, 85 mismatching, no new id). css-layout 1x wall / RSS, 2 runs: base 47.6 s, 45.8 s / 767-774 MB; head 43.7 s, 43.8 s / 773 MB.
## 2026-11-18 — An inline box sits on the line baseline, not centred (Chrome 159)
- **Rule:** an inline non-replaced element's content-area top is `line ascent - its own face ascent` (CSS 2.2 10.8.1). `align_inline_line_baselines` centred the content area in the line box (`node_is_half_leaded`). That is the same place for the line's own font and wrong for any other size.
- **Chrome / base, top of the second box in `<div style="font:F"><span>H</span><X>H</X></div>`:** 16px/1.5 Liberation Sans `<small>` 5 / 4, 12 px span 6 / 5; 16px normal `<small>` 2 / 1, 12 px span 3 / 2. Same-size boxes (`code`, `kbd`, `strong`, a serif span) were already equal.
- **dpr4, first/last ink row of the second run, Chrome / base / head:** Sans `<small>` 33/69 / 29/64 / 33/68; Serif `<small>` 34/68 / 29/62 / 33/66; Sans `<b>` 10.72px 41/69 / 36/66 / 40/70; 12 px span 37/69 / 33/65 / 37/69. This was the "`<small>` 5 rows high" offset.
- **Fix:** `simple_web_html_layout_renderer_layout_foundation.spl`, the `node_is_half_leaded` arm: `aligned_line_y + ascent - inline_content_area_ascent(node) - (bh - content_area_height) / 2`.
- **Pin:** `test/01_unit/browser_engine/inline_box_baseline_alignment_chrome159_spec.spl` (4 cases; 1/4 on base, the guard; 4/4 now).
- **Matrix:** 82 mismatching cells, 0 new; `tt-h1-small-c`, `ln-tt-h1-small-c` and `ln-fontin-fs10-c` left the baseline.
- **Catalog:** 1x and dpr4 equal every row on all 8 pages (the only `<small>` is below the 760 px viewport of the html page).
- **Perf** (html 1x): base 40.88 / 40.44 s, head 40.75 / 40.89 s; max RSS 772-785 MB on both.
- **Measured, NOT landed — device font size at dpr4.** `draw_ir_device_scale` scales `font-size` as round(css) x k. Scaling from `font-size-milli` (round(css x k), with `text_device_painter_dy` reading the ascent at that size) is exact in isolation: `HHHHHHHH` rows, Chrome / base / patched, Sans 13.3 21/56 / 20/55 / 21/56; 14.4 23/61 / 23/60 / 22/61; 15.5 24/66 / 24/64 / 24/66; 17.6 29/76 / 29/77 / 29/76; Serif 22/56 / 22/55 / 22/56; 23/60 / 23/59 / 23/60; 26/65 / 25/63 / 26/65; 29/74 / 29/75 / 29/74. An isolated UA `<h3>` line goes from 9048 to 7150 mismatched px.
  - **Why it still makes two pages worse (dpr4 html 2.60 -> 2.61, forms-media 5.16 -> 5.17):** only the `Feature examples and support` h3 band moves (html rows 2160..2280 +1115 px, forms-media rows 1720..1840 +1425 px; the first html h3, rows 640..720, improves by 304). That h3 is placed too high before the change: Chrome lays the blocks above it out in device px. `--dump-dom` at `--force-device-scale-factor=4` against 1x: forms-media h3 top 429.80 vs 428.53 (text input 33.25 not 33, textarea label 56 not 55, button 33.25, output 18 not 17); html h3 538.32 vs 538.05 (the `<p>` with `kbd` / `samp` / `var` is 24.25 tall). Simple keeps the 1x tops, so the h3 is 5 device rows high on forms-media and 1 on html; the 76 px glyphs of the base (baseline 2 rows lower) hid part of it.
  - **Order to land it:** device-px heights of form controls and of mixed-font lines first, then the size patch.
  - **`sub` / `super` at dpr4:** Blink adds its 1 px in zoomed units: the shift is `k * size / 5 + 1` and `k * size / 3 + 1` device px (14 and 22 rows in a 16 px line at k=4), not k x the CSS shift (16 and 24). With the size patch every sub / sup row is Chrome's (Sans sub 47/83 vs 48/83, sup parent 35/78 exact; Serif exact). Without it the Serif sub bottom moves two rows away (82 -> 80), so it waits for the size patch.
  - **Also seen at dpr4:** a text `<input>` value is painted 14 rows low (47/79, Chrome 33/69); `pen-origin-milli` is not scaled by k and the grayscale path (above 48 device px) ignores it, so a mid-line run starts up to 2 device px right of Chrome's.
- **Trap:** `origin/release/1.0.0` is a shared ref: another lane's fetch moves it under you. Pin the base sha for any base-vs-head file swap.

## 2026-11-18 — percent padding, and bare `span N` grid placement

- **Rule (CSS 2.2 8.4, Chrome 159):** percent padding resolves on ALL four sides against the containing block's INLINE size — the parent content width (block, inline, inline-block, float, flex item), the grid AREA width (grid item), the padding box (absolutely positioned box). `padding-top:25%` in a 100 px grid track is 25 px, never 25% of a height.
- **Was:** `_padding_length_px` (`..._declarations.spl`) returned -1 for a `%` token, which dropped the whole `padding` declaration in every layout context.
- **Fix:** a percent is kept in `Style.pad_{l,t,r,b}_pct` (percent x 1000; the px slot stays 0, so an unresolved reader sees the old "no padding", never a sentinel). The cascade moves both through one slot codec (`padding_slot` / `padding_slot_px` / `padding_slot_pct_milli`: >= 0 px, -1 reject, <= -2 percent) so `padding-top:4px` after `padding:10%` clears only that side. `style_with_resolved_percent_padding(st, containing_w)` (layout_foundation) floors to whole px and clears the percent slots; it is called where each path first binds the child style: the block/inline/float loop (`cst`), `flex_item_percent_style` and the column-flex bindings, the grid loop (against `grid_child_width`), `absolute_child_style` / `absolute_outer_width` (against the padding box).
- **Trap — intrinsic walks read `styles[i]`, not the resolved style.** `intrinsic_text_width` / `flex_item_max_content_width` add the AUTHORED padding, where a percent is 0. Every shrink-to-fit width therefore adds `percent_padding_extra_w(styles[i], resolved)`: the inline / inline-block pen width, the float fit, the abspos shrink-to-fit, and `row_flex_item_auto_intrinsic_w`. Without it an auto-width float around a 50x10 box with `padding:5% 10%` was 50 wide (Chrome 130).
- **Trap — paint reads `styles[i]` too.** Children and text are placed by layout, so they are right (a `padding:10%` page is pixel-identical to its px twin), but paint-side content-box readers (replaced content box, `background-clip/origin:content-box`, input text inset) still see padding 0 for a percent. Open.
- **Bare `span N`:** `normalized_grid_placement` now keeps `span N` (auto start) and turns `span N / L` into the definite `L-N / L`; `grid_placement_start` reads a leading `span` as auto (`parse_int("span 2")` is 2 — it used to become line 2); `grid_placement_span` got the no-slash branch.
- **Auto-placement had to grow with it** (grid loop in `layout_with_style_flow`): the occupancy grid now tracks ROW spans; an auto-row item is searched from a sparse-packing cursor (CSS Grid 8.5 — the old scan from cell 0 back-filled the hole a full-row span leaves, Chrome never does); items with a definite row AND column mark their cells in a pre-pass, whatever the source order; an item spanning only explicit rows stretches to `grid_track_span_size` of them.
- **Chrome 159 / base / head** (x y w h in a 400 px container): block `padding:10%` 0 0 400 90 / 0 0 400 10 / =Chrome, its child 40 40 320 10 / 0 0 400 10 / =Chrome; `width:50%;padding:10%` 280x80 / 200x1 / =Chrome; border-box child 40 40 120 10 / 0 0 200 10 / =Chrome; flex items 180x100 + 220x100 / 100x20 + 300x20 / =Chrome; grid `padding:5%` in a 300 px track 300x30 / 300x1 / =Chrome; `padding-top:25%;height:10px` in a 100 px track h 35 / 10 / =Chrome; abspos 130x90 / 50x10 / =Chrome; `grid-column:span 2` 0 0 220 10 / 0 0 100 10 / =Chrome; `span 2;margin:10%` 22 22 176 10 / 10 10 80 10 / =Chrome; auto item after a full-row span 0 20 100 10 / 240 0 100 10 / =Chrome; `grid-row:span 2` over 30px 30px h 60 / 30 / =Chrome. All 77 measured rects: base 13 equal, head 77 equal.
- **Still open** (`doc/08_tracking/bug/web_percent_padding_unparsed_and_grid_bare_span_2026-11-18.md`): stretch in an implicit grid row (`padding:10%` beside `padding:5%`: Chrome 30/30, here 20/30); sub-px percent padding (floored); `grid-auto-rows`; the paint-side readers above.
- **Spec:** `test/01_unit/browser_engine/percent_padding_grid_span_chrome159_spec.spl` (23 cases, one small page each; 0/23 on base, 23/23 now). `simple_web_padding_units_spec` re-pinned: `padding:10%` used to be the "unsupported unit" example; it now asserts the percent slots (Chrome resolves it), and `10q` is the dropped unit.
- **Gates (blend seed):** catalog 1x base rows = head on all 8 pages (1.14 / 2.35 / 2.19 / 2.43 / 2.33 / 2.40 / 0.68 / 0.42); dpr4 base = head on all 8 (0.65 / 2.60 / 3.42 / 4.06 / 5.16 / 3.81 / 0.50 / 0.30). No catalog page uses percent padding or `grid-column` / `grid-row`, so no row moved. Matrix PASS (979 cells, 85 mismatching, 149 ids, none new, none stale). css-layout 1x wall / RSS, 2 runs: base 45.8 s / 767 MB, 45.3 s / 772 MB; head 43.8 s / 771 MB, 43.9 s / 769 MB.

## 2026-11-19 — grid implicit rows stretch, `grid-auto-rows`, painted percent padding

- **Rule (CSS Grid 11.5 / 12.5, Chrome 159):** a content sized row is only known after EVERY item in it, so stretch (`align-items: normal | stretch`), `center` / `end`, and the offset of every later row cannot be decided while the items are laid out in source order.
- **Was:** one pass. Only items in explicit rows stretched (`grid_row + grid_row_span <= explicit_rows.len()`), an item spanning columns never did, `center` / `end` did nothing, a definite-row item laid out before an earlier row grew kept a stale y, and a row-spanning item put its whole height in its first row.
- **Fix (grid branch of `layout_with_style_flow`, `..._layout_engine.spl`):** pass 1 places + measures each item and records (node, row, span, x, y, w, margins, height, style); rows are then finished (a spanning item shares its deficit equally among the content sized rows it spans; `fr` implicit rows take the largest content per `fr`); pass 2 re-lays ONLY items whose final y moved, that stretch to a content sized row, or that are centred / end-aligned. `grid_row_fixed[row]` (explicit row, or a `grid-auto-rows` length) marks rows that are final up front: their items still stretch in pass 1, so an all-explicit grid pays nothing.
- **`grid-auto-rows`:** `Style.grid_auto_rows`, normalized by `normalized_grid_auto_tracks` (`..._declarations.spl`) to `<N>px` | `auto` | `<N>auto` (`minmax(<length>, auto)`) | `<N>fr`, cycled over the implicit rows. Unsupported tracks (`minmax(<length>, <length>)`, `fit-content()`) drop the declaration. `grid-auto-columns` came later the same day (next 2026-11-19 entry): columns need placement BEFORE sizing.
- **Trap — `style_with_width` is a LAYOUT clone.** It rebuilds the Style from a field list. It dropped the Grid fields, so since percent padding landed a grid container with `padding:5%` (or `max-width:75%`, or a percent block margin) was laid out as a block; it now restores them like `style_with_height`. It also drops paint-only fields (the top / bottom border colours went missing when it was used for paint), so paint must never use it: copy with `Style.copy_from`.
- **Painted percent padding:** paint reads `styles[i]` (percent padding px 0). `web_styles_with_painted_percent_padding(nodes, styles, bx, bw)` resolves it from the laid-out boxes (parent content width past inline ancestors; parent padding box for abspos; grid area = track span starting at the last track at or before the item's left edge) and is applied at the two paint entries only: `paint` (software raster) and `_simple_web_layout_compose_retained` (draw-IR). The retained / hit-index state keeps the authored styles, so a re-layout still sees the percent. No percent on the page = the same array back, no copy.
- **Which lane paints a test page:** `simple_web_engine2d_render_html_pixels` sends a page with text through the draw-IR lane and a text-less page through the software `paint`. A paint fix checked on a text-less probe has only exercised the second; add a text page (or a px twin) before calling it done.
- **Percent padding rounds to nearest** (was floored): `padding:1.7%` of 333 = 5.66: Chrome child y 5.656 / box 21.31, floor 5 / 20, round 6 / 22.
- **Chrome 159 / base / head** (x y w h in a 400 px container): `padding:10%` beside `padding:5%` 100x30 / 100x20 / =Chrome; auto item beside `height:40px` 200x40 / 200x1 / =Chrome; `align-items:center` 10 px item in a 40 px row y 15 / 0 / =Chrome; column-spanning item 200x40 / 200x10 / =Chrome; `grid-auto-rows:50px` third item 0 50 100 50 / 0 1 100 1 / =Chrome; `1fr` rows 60+60 / 60+20 / =Chrome; `span 2;height:60px` beside two 10 px items, second item y 30 / 60 / =Chrome; grid container `padding:5%` children 100 px side by side / 360 px stacked / =Chrome. Paint, whole-frame mismatch vs Chrome: `background-clip:content-box` with `padding:10%` 52.50 % -> 0.00 %; `background-origin:content-box` 52.50 % -> 0.00 %; grid item 3.75 % -> 0.00 %; abspos 17.50 % -> 0.00 %; text page 52.69 % -> 0.32 % (= its px twin).
- **Still open** (`doc/08_tracking/bug/web_percent_padding_unparsed_and_grid_bare_span_2026-11-18.md`): fractional layout units; px-level paint gaps (input background ignores `padding-left`; a flex item's `background-clip:content-box` in the draw-IR lane).
- **Spec:** `test/01_unit/browser_engine/grid_auto_rows_stretch_paint_padding_chrome159_spec.spl` (31 cases; 0/31 on base, 31/31 now).
- **Gates (blend seed):** catalog 1x base rows = head on all 8 pages (1.14 / 2.35 / 2.19 / 2.43 / 2.33 / 2.40 / 0.68 / 0.42); dpr4 base = head on all 8 (0.65 / 2.60 / 3.42 / 4.06 / 5.16 / 3.81 / 0.50 / 0.30) — no catalog page has a content sized grid row with unequal items, `grid-auto-rows` or percent padding, so no row moved. Matrix PASS (979 cells, 82 mismatching, 146 ids, none new, none stale). Mandatory specs 123 / 131 / 68 / 22 green; the three coverage specs fail the same 5 names on base and head. css-layout 1x wall / RSS, 2 runs: base 45.2 s / 769 MB, 46.5 s / 754 MB; head 43.8 s / 770 MB, 43.8 s / 772 MB.
## 2026-11-18 — Lines and form controls take their device-px height at device scale > 1 (Chrome 159)

- **Rule:** at `--force-device-scale-factor=k` Chrome lays out in device px, so a box is a whole number of DEVICE px tall. Measured (`getBoundingClientRect`, CSS px, k = 1 / 2 / 3 / 4, `padding:8px;border:1px` controls in a 16px/1.5 Liberation Sans page):
  - text `<input>` and `<button>`: 33 / 33.5 / 33 / 33.25. The `normal` line of the 13.333 px UA font is the face's per-part rounded sum at 13.333k px: 15, 31, 45, 61.
  - `<select>`: 35 / 35 / 34.667 / 34.75. Its inner block padding is round(1.5k) device px (2, 3, 5, 6), not k x 2.
  - `<textarea>` (2 rows, monospace): 48 / 49 / 48.667 / 49.5; its label 55 / 55.5 / 55.667 / 56 (the textarea plus the strut's device descent, 26 at k=4).
  - a 16px/1.5 line holding a 13 px monospace `code` / `kbd`: 24 / 24 / 24.333 / 24.25 (97 device px at k=4: ascent 70, descent 27).
- **Was:** every height stayed whole CSS px x k, so each block below such a box was up to 2 device px off and the offsets added up: the forms-media h3 under the form sat 5 device rows high (Chrome top 429.80 at k=4, 428.53 at 1x).
- **Fix (`simple_web_html_layout_renderer_layout_foundation.spl`):**
  - `align_inline_line_device_dy` now mirrors the DESCENT too and returns the line's device height minus k x (CSS ascent + descent). `align_inline_line_baselines` hands it back as `InlineLineAlignment.height_frac_milli` (milli CSS px), only where the baseline pass set the line height and no `middle` / top / bottom box is on the line.
  - The block cursor adds it to `cy_frac` at its seven line-advance sites (`..._layout_engine.spl`), so it reaches the parent through `end_frac_milli` like every other residual.
  - `g_box_device_extra_h` (device px per node, k > 1 only): the form-control branch records `form_control_device_extra_h`, the block path records its own end residual. A line reads it for its atomic boxes: above the baseline for a bottom-edge box (textarea, checkbox), below it otherwise.
  - `style_device_font_milli` / `style_is_ua_control_font`: the UA control font is carried as 13 px with a 1.2 ratio; device metrics use the real 13.333 px / `normal` (61 device px at k=4, where 13 x 4 x 1.2 gave 62).
- **Trap — an inline container must not take the fraction.** A `<small>` runs its own text through the same line pass; adding its 0.75 px excess to its cursor made the inline box 20 px instead of 19 and moved its run 8 device rows up (`inline_box_baseline_alignment_chrome159_spec` AC-4: 25/60 against Chrome 33/69). `height_frac_milli` is 0 when the line's container is `display:inline`; the line around it reads the box's device reach from its struts.
- **Re-pins toward Chrome** (that spec, AC-4, second run first/last row, Chrome / was / now): Sans `<small>` 33/69 / 33/68 / 34/69; Serif `<small>` 34/68 / 33/66 / 34/68; Sans `<b>` 10.72 px 41/69 / 40/70 / 41/69. The 12 px span stays 37/69.
- **Matrix:** PASS, 979 cells, 82 mismatching, no new and no stale id. Catalog 1x equals every row.
- **Boxes stay CSS-snapped:** only the cursor moves. An input's own border box still paints 132 device rows, not 133. Lines 2..n of a wrapped run and later lines of the same block keep k x CSS.
- **Device font size, landed with it** (the patch held by #10262): `draw_ir_device_scale` scales `font-size` from `font-size-milli` (14.4 px -> 58 device px), `text_device_painter_dy` reads the ascent at that whole size, and `vertical_align_baseline_shift_device` is `k * size / 5 + 1` (sub) / `k * size / 3 + 1` (super) device px.
- **Pin:** `test/01_unit/browser_engine/device_px_block_height_chrome159_spec.spl`. Base 1/3 (the 1x guard), head 3/3.
  - AC-1 marker rows at k=4, Chrome = head / base: R197-236 G440-479 R768-807 G941-980 R1078-1117 G1215-1254 / R196-235 G440-479 R764-803 G936-975 R1072-1111 G1208-1247.
  - AC-3 first/last ink row, Chrome / base / head: 14.4 px 23/61 / 23/60 / 22/61 (only the baseline row is pinned); 15.5 px 24/66 / 24/64 / 24/66; 17.6 px 29/76 / 29/77 / 29/76; `sub` 48/83 / 49/84 / 48/83.
- **Catalog dpr4, base 5bd3ff5651b / heights only / heights + font size:**

  | Page | Base | Heights | + font size |
  |---|---|---|---|
  | overview | 0.65 | 0.62 | 0.62 |
  | html | 2.60 | 2.39 | 2.37 |
  | css-layout | 3.42 | 3.27 | 3.25 |
  | css-paint | 4.06 | 3.56 | 3.54 |
  | forms-media | 5.16 | 3.30 | 3.28 |
  | animation (time-sampled) | 3.81 | 3.39 | 3.34 to 3.37 |
  | evidence | 0.50 | 0.50 | 0.50 |
  | tab-bar | 0.30 | 0.30 | 0.30 |

- **Perf** (forms-media at dpr4, 2 runs): base 114.1 / 112.5 s, 2903 / 2924 MB; head 104.9 / 117.6 s, 2919 / 2928 MB.
- **Open:** device-px HEIGHT of the painted control box (bottom border 1 row high at k=4); the 14.4 px cap top (22, Chrome 23); a `<select>` padding split (top / bottom) was not measured, only its sum.

## 2026-11-19 — empty boxes are 0 px high; `grid-auto-columns` and implicit grid columns

- **Rule (CSS 2.2 10.6.3, Chrome 159):** an auto-height box with no in-flow content is 0 px high. **Was:** `if h < 1: h = 1` at the end of the block path and of the three flex paths (row, wrapping row, column) in `..._layout_engine.spl`, so every empty box was 1 px and shifted its followers by 1 px. **Fix:** the four floors are deleted.
- **Trap — the self-collapsing test leaned on that floor.** It read `child_height <= 1` ("0 and 1 both mean no content"), so a block with 1 px of REAL content (a 1 px rule inside a margin box) also lost its margins. It is `child_height == 0` now. Any other "is it empty" test must use 0 too.
- **Zero height is not "no box".** Readers that test `bh > 0` (hit testing, text-input overlays, gradient tiles, the scroll-reason probe) now skip an empty box. That is what Chrome does; do not re-add a floor to feed them.
- **Rule (CSS Grid 7.6 / 8.5 / 12.5):** the column count of a grid is not its template. A definite column or a span past the template, and column flow once the rows are full, open implicit columns sized by `grid-auto-columns`.
- **Was:** the grid branch ran only with a `grid-template-columns` (else the block path), sized the columns before placing anything, clamped out-of-template placements into the template, and column flow without template rows filled column 1 downwards.
- **Fix (`..._layout_engine.spl`):** placement is its own pass, `grid_item_placements` (the former in-loop code, unchanged in logic), run BEFORE the columns are sized; `grid_item_line_extents` gives the placement grid (row flow: max(template, furthest definite column / span); column flow: one spare column per item, rows = template rows, else the rows the items name, else 1). The grid keeps the columns it used. `grid_column_sizes_with_implicit` then sizes template + cycled `grid-auto-columns` tracks. `Style.grid_auto_columns` uses `normalized_grid_auto_tracks` with `percent_definite` (a whole `N%` stays `<N>%` of the grid width; for rows a percentage is still `auto`).
- **`auto` implicit columns** are the widest margin box lying in them alone (`row_flex_item_auto_intrinsic_w`, or the authored width), then share the free width equally (`justify-content: normal`). `Style.justify_content` defaults to `"flex-start"`, so that value means "not authored" here; an authored `start` / `center` / `end` leaves the columns at their content. Implicit `fr` columns take the free width instead.
- **A grid whose columns all come from the template takes the old sizing path** (`grid_column_count == grid_explicit_column_count`), so existing pages pay one placement pass and nothing else.
- **Grid enters with no template only when** `grid-auto-columns` is set or the flow is `column`. A plain `display:grid` with neither is still the block path (one full-width column either way).
- **Measure before fixing a residue line.** Two of the four residue entries this lane was given were not gaps: `<textarea style="padding:10%;width:100px;height:40px">` is 182 x 122 in Chrome AND here (the recorded "Chrome 100x80" was wrong), and a percent `margin-top` on a grid container is applied (20 px for 5% of 400) wherever the parent really is a formatting-context root. The failing probe used `display:flow-root`, which is not parsed, so the parent was a plain block and ANY first-child top margin collapsed through it.
- **Chrome 159 / base / head** (x y w h in a 400 px container): empty block 400x0 / 400x1 / =Chrome; empty `align-self:start` grid item 200x0 / 200x1 / =Chrome; 10 px item after an empty grid row y 0 / 1 / =Chrome; 5 px block after `margin:8px 0` around 1 px of content y 18 / 9 / =Chrome; `grid-auto-flow:column;grid-auto-columns:100px` third item 200 0 100 10 / 0 20 400 10 / =Chrome; template `100px` + `grid-auto-columns:50px` in column flow, third item 150 0 50 10 / 0 20 100 10 / =Chrome; `grid-column:3` past a `100px` template with `grid-auto-columns:60px` 160 0 60 10 / 0 10 100 10 / =Chrome; `auto` columns around 30 px and 70 px boxes 180 + 220 / 400 stacked / =Chrome; rows `20px 20px` in column flow, fifth item 200 0 100 20 / 0 0 400 1 / =Chrome; `padding:10%` item in a 100 px implicit column 115 5 100 30 / 5 19 400 90 / =Chrome.
- **Still open** (`doc/08_tracking/bug/web_percent_padding_unparsed_and_grid_bare_span_2026-11-18.md`): `display:flow-root` (margin collapsing, float enclosure, float avoidance); an empty inline box opens an 18 px line; an empty block's margin does not collapse through its parent; an empty `<li>` is 0 (Chrome 18, marker line); grid free width is shared in whole px, no `justify-content` track distribution, no auto inline margin on a grid item, paint-side percent padding reads template tracks only; `<input>` / `<select>` / `<button>` padding does not size the control.
- **Spec:** `test/01_unit/browser_engine/layout_residuals_chrome159_spec.spl` (35 cases; 2/35 on base, the two unchanged-behaviour guards; 35/35 now).
- **Gates (blend seed):** catalog 1x base rows = head on all 8 pages (1.14 / 2.35 / 2.19 / 2.43 / 2.33 / 2.40 / 0.68 / 0.42); dpr4 measured base = head on all 8 (0.62 / 2.37 / 3.25 / 3.54 / 3.28 / 3.37 / 0.50 / 0.30); the empty-box change alone was measured separately with the same result, and the css-layout 1x frame is byte-identical base vs head. No catalog page has an empty auto-height box that moves a painted pixel, or an implicit grid column, so no row moved. Matrix PASS (979 cells, 82 mismatching, 146 ids, none new, none stale). Mandatory specs 123 / 131 / 68 / 22 green, the four grid / percent / device-px specs green; of 90 more layout specs 10 fail the same 18 names on base and head. css-layout 1x wall / RSS, 2 runs: base 46.5 s / 770 MB, 52.4 s / 767 MB; head 46.4 s / 769 MB, 46.5 s / 766 MB.
## 2026-11-19 — Form-control chrome paints as Chrome 159 (vector parts, native frame, UA colours, device height)

- **Rule (Chrome for Testing 159 on Linux, screenshots at device scale k = 1 and 4, grip also at 2 and 3):**
  - Checkbox / radio are vectors on a `side` CSS px square scaled by k: a 1 CSS px #767676 ring whose centre line is 0.5 px inside the square (corner radius 2 px, a circle for a radio) over white; checked checkbox = #0075ff rounded square, no ring, white check stroked 0.16 x side through (0.2, 0.5) (0.4, 0.7) (0.8, 0.2) x side; checked radio = #0075ff ring + dot of radius 0.3 x side.
  - `<select>` arrow: chevron (0,0) (4k,4k) (8k,0) whose box starts at int(inner right - 11.5k), centred on the control's middle row, stroked **2 device px at every scale**.
  - `<textarea>` grip: two **aliased** lines (14k,7k)-(7k,14k) and (14k,10.5k)-(10.5k,14k) (10.5k rounds half up: 11, 21, 32, 42), k px wide, black at 60 %, measured from a point 16k px inside the padding box's bottom-right corner; then the same lines k px lower in white at 60 %, clipped at row 14k - 1 (row 14 at k = 1).
  - An unstyled text field / textarea / menulist is a 1 px #767676 frame at the outer edge of the UA border area over white; a button the same over #efefef. A control does not inherit `color` (FieldText / ButtonText = #000); a button with an author border keeps the #efefef ButtonFace.
  - Disabled (on #fff): field frame #d0d0d0 over #f8f8f8, text #545454; button #d0d0d0 over #eeeeee, text rgba(16,16,16,.3); select = the field at `opacity: 0.7` with #808080 text and arrow (#a5a5a5 on #fafafa); checkbox ring #d1d1d1 over #f8f8f8.
- **Was:** a square #2563eb outline with a filled inner square / circle, a 7-px filled triangle, no grip, a 2 px #767676 border on white for every field and button, the parent's `color` inherited into controls, and the painted box k x its CSS height at k > 1.
- **Fix:**
  - `form_control_chrome.spl` (new): the parts as ARGB spans in device px. Integer 1/64 px geometry, exact-area coverage by 8 x 8 supersampling of the edge pixels, runs merged horizontally and vertically, a 32-entry cache per (part, size, k, state).
  - `..._paint_draw_ir.spl`: `_html_draw_ir_chrome_span_commands` lowers a span to one rect. At k > 1 the rect carries `device-rect` = "dx,dy,w,h"; `draw_ir_device_scale.spl` moves the scaled CSS origin by (dx, dy) and sets the device size, so a part is sharp at every scale. `device-extra-height` grows a control's box (and its border / content / hit rect) by `box_device_extra_h_at`.
  - `..._paint_primitives.spl` / `..._paint_raster.spl`: the staging raster blends the same spans (`fb_chrome_spans_clip`), so the two lanes stay pixel-equal (the legacy widget-mode specs compare them).
  - `..._core.spl`: `form_control_ua_box_decls` adds the UA colours and `resize: both`; `_apply_native_control_look` replaces the old select-only white fill for every control the author did not restyle (`_select_author_styled`): border 1 px, the hidden border px moved into the padding, so the content box does not move.
  - Input value text (Draw IR lane): `_html_draw_ir_input_value_command` shapes the value with real advances on a line box centred in the content box, for fonts above 8 px -- the rule the raster already had (`use_ttf`). The Draw IR lane was still on the fixed-pitch cell model: `Simple` in a default field sat 3 rows low and 7 px too wide (rows 9..17, cols 5..50; Chrome 6..17, 5..43).
- **Traps:**
  - **A 1 px anti-aliased stroke is a Skia HAIRLINE**, not a filled stroke: at k = 1 the ring pixels are not the exact area of a 1 px ring (top-centre of the radio is 0x99, a full pixel would be 0x76). Those coverages are tables (`_FCC_RADIO_13_HAIRLINE`, `_FCC_BOX_HAIRLINE_EDGE`); from k = 2 the ring is the geometric stroke.
  - **Engine2D applies a node's opacity to the rects that name it as `parent_id`.** Pre-multiplying the span colour by `opacity_pct` applied it twice (disabled select arrow #bfbfbf, Chrome #a5a5a5). The old chevron did exactly that.
  - **The Draw IR lane has no `background-clip`** (the prop is emitted, nothing reads it): a translucent fill always runs under a translucent border. The disabled frame colours are therefore solved for a white page; on a coloured page they are off.
  - **Corner radius differs between the lanes**: `border-radius: 1px` differs by 4-5 px per box between the raster and Engine2D, and the widget-mode specs require 0. The native frame stays square (Chrome: outer radius 2.5 px, the 4 corner px are page colour).
  - A sample exactly on a stroke's cap: inside at the start cap, outside at the end cap. Without it the aliased grip is one diagonal too long at k = 2..4.
  - `pass` is a reserved word (a loop variable named `pass` fails to parse with "expected pattern").
  - `examples/` scripts that write a PPM need `SIMPLE_EXECUTION_MODE=interpreter`; in the default mode `encode_ppm_p6` wrote a broken header.
- **Spec:** `test/01_unit/browser_engine/form_control_paint_chrome159_spec.spl` (11 cases: 0/11 on base 0251987783a, 11/11 now). It embeds Chrome's 13 x 13 pixels of the four checkable states and of the arrow block, and measures every fact relative to the control's own box.
- **Per-control pixels differing from Chrome by more than 8 (band of the test page; Chrome / base / now):**

  | control | 1x base -> now | 4x base -> now |
  |---|---|---|
  | checkbox | 52 -> 0 | 977 -> 467 |
  | checkbox checked | 169 -> 25 | 2748 -> 521 |
  | checkbox disabled | 52 -> 0 | 969 -> 433 |
  | checkbox checked disabled | 169 -> 0 | 2794 -> 408 |
  | radio | 76 -> 0 | 863 -> 632 |
  | radio checked | 143 -> 26 | 1696 -> 877 |
  | radio disabled | 68 -> 0 | 851 -> 549 |
  | radio checked disabled | 132 -> 2 | 1679 -> 731 |
  | select | 279 -> 224 | 5633 -> 5102 |
  | select disabled | 423 -> 220 | 6618 -> 4992 |
  | textarea | 545 -> 540 | 11666 -> 5055 |
  | textarea disabled | 963 -> 541 | 15235 -> 5054 |
  | text input | 793 -> 277 | 15177 -> 9023 |
  | text input disabled | 1194 -> 277 | 19083 -> 9028 |
  | button | 627 -> 121 | 10563 -> 2133 |
  | button disabled | 714 -> 75 | 11776 -> 2035 |
  | catalog-styled select | 352 -> 281 | 4207 -> 2506 |
  | catalog-styled textarea | 625 -> 620 | 12537 -> 5540 |
  | catalog-styled input | 453 -> 337 | 6591 -> 3230 |
  | catalog-styled button | 1077 -> 159 | 17091 -> 1017 |

  The 4x rows of the default controls include a 2-row layout offset of the whole band; aligned on the box the parts are checkbox 823 -> 79, checked 2661 -> 81, radio 728 -> 152, checked 1546 -> 282.
- **Re-pins:** `simple_web_html_layout_renderer_coverage_spec` radio example `_distinct` 3 -> 28 (the Chrome parts are anti-aliased; pixels off Chrome on that page 280 -> 176); `simple_web_renderer_spec` widget-mode input pixel #f5f5f5 -> #ffffff (inside the white Field).
- **Gates (blend seed):** specs `simple_web_renderer_spec` 123/123, `browser_renderer_spec` 131/131, `layout_renderer_box_geometry_chrome159_spec` 68/68, `web_device_scale_spec` 22/22, `form_control_chrome159_geometry_spec` 42/42, `device_px_block_height_chrome159_spec` 3/3; matrix PASS, 979 cells, 82 mismatching, no new and no stale id; catalog 1x 1.14 / 2.35 / 2.19 / 2.43 / **2.27** (row 2.33) / 2.40 / 0.68 / 0.42; catalog dpr4 0.62 / 2.37 / 3.25 / 3.54 / **3.14** (row 3.28) / 3.37 / 0.50 / **0.26** (row 0.30). Rows lowered to the measured values.
- **Perf** (forms-media at dpr4, 2 runs, wall / peak RSS): base 114.1 / 126.1 s, 2884 / 2889 MB; head 122.3 / 119.0 s, 2916 / 2944 MB.
- **Open:**
  - Native frame corners are square (4 px per control at 1x).
  - The checked mark / dot differ by 25 / 26 edge px at 1x: Skia's small strokes are ~0.07 px bolder than their exact area.
  - **Device-px WIDTH of a control at k > 1 is not modelled** (layout): at k = 4 Chrome's default text input is 719 device px wide, here 740; the catalog's styled input 759 vs 780, select 289 vs 292, button 143 vs 144, textarea 775 vs 772. This is most of what is left of forms-media at dpr4.
  - The UA control font is carried as 13 px, Chrome's is 13.333 px: a textarea's monospace run is 160 px for 20 columns where Chrome has 161, so the textarea is 1 px narrower (181 vs 182 default, 193 vs 194 in the catalog) and its text sits 1 row low.
  - `test/03_system/app/browser/feature/browser_checkable_control_rendering_spec.spl` does not run on base (`dispatch_dom_event` not found on `BrowserSession`, a semantic error before any example). Its Draw IR pins describe the old flat chrome (frame colour #f8fafc, `border-radius` props, pixel (2,2) = accent); they need re-pinning to the parts when the spec is repaired. The `_checkable_frame` / `_checked_indicator` commands are kept as transparent state carriers.

## 2026-11-19 — Glyph advances stay exact past 8 (face, size) pairs (Chrome 159)

- **Symptom:** on a page with more than 8 (face, size) pairs the glyphs of a run sat `round(advance)` px apart and all on LCD phase 0, so their x positions drifted from Chrome's along the line. Twelve sizes of one face were enough; `html` in the catalog has more than 8 pairs.
- **Root cause** (`FontRenderer.get_glyph_advance_milli`, `text_layout/font_renderer.spl`): the milli advance cache has 8 (face, size) slots, evicted round-robin. On a slot miss the function asked the renderer's `GlyphCache` first, and a rasterised glyph carries only a whole-pixel advance, so a glyph that had been drawn before its slot was evicted answered `advance * 1000` and the refilled slot kept that. `H` at 13 px in Liberation Sans: 9000 milli; Chrome 159 measures 9.390625 px (`hmtx` 1479 / 2048 em).
- **Fix:** with a selected outline blob the glyph cache no longer answers. The index lane and the direct lane below it read `meta[18]`, the unrounded `hmtx` advance, without a raster, so a refill is the same number as a first fill. The cached whole pixel is the fallback for a glyph neither blob lane can answer, and still the direct answer on a backend without a blob.
- **Measured** (520x340, twelve lines of `Hamburgefonstiv Qy,.:;19`, 12 to 23 px, pixels with a channel more than 8 from Chrome / summed |delta|): 13272 / 1,585,925 -> 5506 / 479,830, no line worse. Catalog 1x `html` 2.35 -> 1.78, other pages unchanged; dpr4 unchanged on all 8 pages; combo matrix 146 / 146 ids.
- **Cost:** a page whose pairs were all past the eighth now rasters quarter-phase cells it never had: 36 paragraphs in nine faces, cpu_simd, 32.1 -> 36.7 s. The twelve-size page did not move (16.1 / 17.0 s -> 15.9 / 13.6 s).
- **Trap:** the order of measuring and drawing decided the pens, so two renders of the same text could differ. Anything that keeps a glyph out of `GlyphCache` (the LCD raster deferral of the entry above put its frames in for exactly this reason) no longer changes advances on the blob backend.
- **Trap for a scratch page (fixed 2026-11-19, see "Bare text in a `<div>` takes the Draw IR text lane"):** bare text directly inside a `<div>` was drawn in gray (no LCD) with other glyph shapes, 19908 mismatching pixels on the twelve-size page against 13272 with the text in a `<span>`. It was the raster lane, not the absolute position.
- **Spec:** `test/01_unit/browser_engine/glyph_advance_eviction_exact_chrome159_spec.spl` (AC-1 the advance after an eviction and a draw, AC-2 four Chrome pixel windows on the twelve-size page).

## 2026-11-19 — Vulkan font atlas repacks incrementally again (one sequence step per batch, 12 parked owners)

- **Symptom:** the Vulkan lane repacked all 1,048,576 atlas pixels (`font_atlas_pack_u32_to_u8`, about 5 s each on the interpreter lane) for nearly every text run: `pack_full=36 pack_incremental=0` on a 36-paragraph page, 177 s of a 211 s render against 38 s on cpu_simd.
- **Cause 1** (`_lcd_publish_cells`, `text_layout/font_renderer.spl`): one LCD run publishes dirty cells from up to three passes (staging, the phase cells of `_lcd_apply_pen_phases`, the phase-0 cells of `_lcd_resolve_deferred_cells`), and each publish stepped `atlas_owner_sequence`. A run that added both a phased and a phase-0 cell read `host + 2`, which the consumer's `+1` rule (`vulkan_font_mirror_continuity`) correctly takes for a batch it never saw. One face is enough: twelve sizes of Liberation Sans took 12 full packs. Now the sequence steps once per staged batch and later passes only add rects.
- **Cause 2:** `FONT_ATLAS_PARK_MAX` was 4, so a page cycling through more than five faces wiped an owner on every return (re-seeded sequence, every glyph inserted again, full pack). It is 11 (12 owners: three generic families in four styles) and `VULKAN_FONT_ATLAS_MIRROR_MAX` follows it; raising only the consumer's cap changes nothing, which is what the earlier lane measured.
- **Measured** (lavapipe, wall, `pack_full / pack_incremental`), Vulkan base -> head: twelve sizes of one face 71.8 s, 12 / 0 -> 15.1 s, 1 / 11; nine faces with new glyphs each round 152.2 s, 27 / 0 -> 66.2 s, 9 / 18; 36 paragraphs in nine faces 211.0 s, 36 / 0 -> 83.4 s, 9 / 27; catalog `html` 108.1 s, 17 / 7 -> 42.9 s, 4 / 20 (cpu_simd 44.9 s). Frames byte-equal base to head on every page.
- **Trap:** the advance fix of the entry above is what exposed cause 1 on pages with more than 8 (face, size) pairs. Before it their pens were whole pixels, every cell was phase 0, and a batch published once.
- **Trap:** never fix this on the consumer by accepting a gap. A gap also means a dirty batch that never reached the backend.
- **Still open:** the first batch of each owner is a full pack (9 x about 5 s on the nine-face page). See the bug record.
- **Spec:** `test/02_integration/gpu/vulkan_font_atlas_incremental_repack_spec.spl` (one LCD run is one step and reads INCREMENTAL; nine interleaved owners all restore; the mirror cap covers the park cap). Count with `SIMPLE_VK_TIMING=1`, trace with `SIMPLE_VK_ORDER_TRACE=1`.
## 2026-11-19 — Form-control follow-ups: rounded native frame, document-mode box-sizing, 13.333px control font, device-px control width

- **Rule (Chrome for Testing 159 on Linux, `--screenshot` at k = 1..4 and `--dump-dom` geometry, Liberation Sans / DejaVu Sans Mono):**
  - The native frame of an unrestyled text field, menulist, textarea and push button is a k px stroke whose centre line is k/2 inside the box with a corner radius, over a fill of the same rounded rect. Field / menulist / textarea are **not anti-aliased**, a button is. First ring column of the top rows of a text field: k=1 `1`, k=2 `3 1 1 0`, k=3 `5 3 2 1 1 0`, k=4 `7 5 4 3 2 1 1 0`: centre-line radius 2k at k = 1..3 and 8.5 device px at k = 4. A button at k = 1 is a Skia hairline: row 0 `ff a2 97 76`, row 1 `a2 ab ef`.
  - `box-sizing` depends on the document mode. Standards (a doctype): text, password, email, number, date, range, file inputs and `<textarea>` are content-box (`width:40px;height:16px;padding:2px` is 48x24, textarea 46x22); search, color, button / submit / reset, checkbox, radio, `<select>`, `<button>` are border-box. Quirks (no doctype): html.css adds `input:not([type=image]), textarea { box-sizing: border-box }` (40x16 for both).
  - The UA control font is 13.3333px. `Simple` in a default field inks columns 5-43 (5-42 at 13 px).
  - `<textarea cols=N>` content is `ceil(N x avgCharWidth) + 15`: 30 / 62 / 102 / 182 / 343 px boxes for N = 1 / 5 / 10 / 20 / 40 (the old `8N + 15` pins 181 / 101 / 341 and the catalog's 193 were 1-2 px short; Chrome is 182 / 102 / 343 / 194 in both modes).
  - Chrome lays out in device px: a control's device width is the same rule at k x the font size, not k x its CSS width. k = 4: text input 19 x 31 + 98 + 32 = 719 (4 x 185 = 740), textarea 643 + 60 + 24 = 727 (728), select ceil(136.41) + 88 = 225 (228); catalog-styled 759 / 775 / 289.
  - A check mark is #3b3b3b instead of white when the accent colour's WCAG contrast against white is below 3 (#8686ff 3.06 white, #8888ff 2.996 dark, #22c55e dark).
- **Was:** a square frame; every `<input>` border-box and every `<textarea>` content-box whatever the doctype; the control font carried as 13 px; `8N + 15` textarea columns and, at any other font size, the UA numbers times `font_size / 8` (a 16px input was 354 px wide, Chrome 215); k x the CSS width at k > 1; a white check mark on every accent colour.
- **Fix:**
  - `form_control_chrome.spl`: `chrome_frame_spans(kind, w, h, k)` builds ring and fill from four corner blocks (aliased for a field, 8 x 8 supersampled for a button, the k = 1 button hairline as a table) plus plain rects for the straight runs; a translucent (disabled) fill stops at the ring's inner edge. `_fcc_accent_needs_dark_mark` picks the mark colour.
  - `Style.native_frame` (set by `_apply_native_control_look`, copied by `copy_from`) marks the control. Outside widget mode the Draw IR lane suppresses the box (`_html_draw_ir_widget_suppressed_box`) and pushes `_html_draw_ir_native_frame_commands`; the staging raster skips the box's fill / border and blends the same spans. `Style.bg` / border keep their colours for every other reader.
  - `HNode.standards_mode` on the root node (`html_source_has_doctype`); `form_control_ua_box_decls(node, standards_mode)`. The UA decls are part of the cascade memo key, so the mode needs no key of its own.
  - `tag_defaults`: controls carry `font_size_milli = 13333` (`font_size` stays 13).
  - A `<button>` label wider than its whole-px content box used to stay on one line via a `label_slack` in the `#text` layout (a flex row snapped `CSS Paint` to 79 px where Chrome has 79.5). Removed 2026-11-22: flex items now carry LayoutUnit widths and the tab row stays one line without it.
  - `form_control_content_w_for_face(tag, face, cols, scale, font_milli, k)`: Chrome's rule on the face metrics (Liberation Sans xAvgCharWidth 1187 / bbox 3780, DejaVu Sans Mono 1233, of 2048), in device px.
  - `g_box_device_extra_w` / `device-extra-width`: the width twin of `device-extra-height`; `draw_ir_device_scale.spl` grows (here: shrinks) the box and its border / content / hit rect; the select arrow and the textarea grip follow the right edge.
- **Traps:**
  - A spec page without a doctype measures QUIRKS values in Chrome. `--dump-dom` of `document.compatMode` tells which (`BackCompat` / `CSS1Compat`).
  - The frame radius is not 2k at k = 4 (8.5). Fitting the outer and the inner edge separately looked like a 0.5 px sampling offset; it is one radius.
  - `_html_draw_ir_widget_suppressed_box(cmd, true, false)` is the way to make a box command paint nothing while keeping its rects, state props and children.
  - **More than 8 (face, size) pairs on a page used to evict glyph advance slots**: the two new 13.333px faces (Liberation Sans, DejaVu Sans Mono) then shifted the LCD raster of unrelated runs with byte-identical Draw IR (forms-media 2.27 -> 4.45 at 1x on the old base). Fixed upstream by d3ab3e1b873 (exact hmtx refill) while this lane ran; on it forms-media is 2.17. When text far from a change moves, count the page's (face, size) pairs.
  - A catalog regression can come from a page with no form control on it: run the catalog before trusting the per-control numbers.
  - Specs keep reading the files on disk: no source edits while a spec batch runs.
- **Spec:** `test/01_unit/browser_engine/form_control_frame_metrics_chrome159_spec.spl` (11 cases; AC-1..9 0/9 on base c824eadfdb0, AC-10 red on base by its numbers, AC-11 a wrap guard that is green on base; 11/11 now).
- **Re-pins (all toward Chrome, measured 2026-11-19):** textarea width 181 -> 182, 101 -> 102, 341 -> 343, 193 -> 194, 113 -> 114, 353 -> 355 (`form_control_chrome159_geometry_spec`, `form_control_authored_size_chrome159_spec`, `form_control_ua_font_reset_chrome159_spec`, `form_control_intrinsic_width_spec`); `form_control_content_w_for_face` unit rows take the new signature (DejaVu 175 -> 176, 335 -> 337).
- **`browser_checkable_control_rendering_spec` runs again (1/1):** `dispatch_dom_event(author_id, ...)` was removed by 8282e432b3b; the spec now dispatches through `dispatch_dom_event_route(system_dom_route(index, id), ...)`. Hit keys are DOM routes (`path:0` .. `path:2`). The flat-chrome pins are re-pinned to Chrome's pixels for that fixture: corner px page colour, unchecked fill #ffffff (was #f8fafc), disabled #f8f8f8, radio ring top #2abe61 (within 8), check mark on #22c55e #3b3b3b (was the accent colour); the `_checkable_frame` / `_checked_indicator` commands are transparent state carriers and the `_part_<n>` rects paint.
- **Per-control pixels differing from Chrome by more than 8 (band of the test page; base c824eadfdb0 -> now):**

  | control | 1x | 4x |
  |---|---|---|
  | select | 224 -> 64 | 5102 -> 4406 |
  | select disabled | 220 -> 202 | 4992 -> 4292 |
  | textarea | 540 -> 295 | 5055 -> 2100 |
  | textarea disabled | 541 -> 294 | 5054 -> 2047 |
  | text input | 277 -> 194 | 9023 -> 7848 |
  | text input disabled | 277 -> 196 | 9028 -> 7843 |
  | button | 121 -> 64 | 2133 -> 2131 |
  | button disabled | 75 -> 10 | 2035 -> 2005 |
  | catalog-styled select | 281 -> 125 | 2506 -> 1473 |
  | catalog-styled textarea | 620 -> 359 | 5540 -> 2325 |
  | catalog-styled input | 337 -> 258 | 3230 -> 1617 |
  | catalog-styled button | 159 -> 126 | 1017 -> 909 |

  Checkbox / radio rows are unchanged (0 / 25 / 0 / 0 / 0 / 26 / 0 / 2 at 1x).
- **Gates (blend seed):** specs `simple_web_renderer_spec` 123/123, `browser_renderer_spec` 131/131, `layout_renderer_box_geometry_chrome159_spec` 68/68, `web_device_scale_spec` 22/22, `form_control_paint_chrome159_spec` 11/11, `form_control_chrome159_geometry_spec` 42/42, `form_control_frame_metrics_chrome159_spec` 11/11, `device_px_block_height_chrome159_spec` 3/3, the other form / input specs green; `simple_web_html_layout_renderer_coverage_spec` 37/39 with the same two failing names as base (`rasters rounded corners under fractional opacity`, `rasters a text run carrying decoded numeric entities`); matrix PASS, 979 cells, 82 mismatching, 146 ids = 146 baselined (no new, no stale); catalog 1x 1.14 / 1.78 / 2.19 / 2.43 / **2.17** (row 2.27) / 2.33 / 0.68 / **0.34** (row 0.42); catalog dpr4 0.62 / 2.37 / 3.25 / 3.54 / **3.06** (row 3.14) / 3.37 / 0.50 / **0.21** (row 0.26). Rows lowered to the measured values.
- **Perf** (forms-media at dpr4, 2 runs, wall / peak RSS): base b6d1f929081 118.4 / 118.0 s, 2873 / 2859 MB; head 118.4 / 116.5 s, 2873 / 2867 MB.
- **Open:**
  - Default controls at k = 4 sit 2-3 device rows above Chrome's (text input top 32 vs 34, select 36 vs 39, checkbox 40 vs 42): the line's device baseline is not applied to an inline control's box. This is most of what is left of the default-control rows at 4x.
  - Boxes after a control on the same line keep their CSS-snapped x at k > 1 (up to `k x w - device w` px right of Chrome's); a `<button>`'s fractional device width is not modelled (135 vs 136 at k = 4).
  - FIXED 2026-11-20 (see below): an `<input>` / `<textarea>` at `font-size:16px` was 209 / 214 px against Chrome 215 / 221.
  - The k = 3 frame differs from Chrome by one px per corner (Chrome's inner edge is not symmetric there); a button's anti-aliased corner at k = 4 differs by up to 15 levels on ~6 px per corner; a listbox (`<select multiple>`) frame is anti-aliased in Chrome and aliased here.
  - `simple_web_browser_engine_production_hardening_spec` still expects an `id:stage` hit key; hit keys are `path:` routes since 8282e432b3b.

## display:flow-root (2026-11-19)

- `flow-root` is now a supported display keyword (`is_supported_display_keyword`, `declarations.spl`, `decl_apply.spl`); `st.display == "flow-root"`. Because margin-collapse-through predicates require display block/list-item and `float_ctx_establishes_bfc` treats every non-block display as a BFC root, it blocks parent-child margin collapse, contains floats and is narrowed beside a preceding float with no other change.
- Spec: `test/01_unit/browser_engine/display_flow_root_chrome159_spec.spl` (6 examples, Chrome 159 measured). Trap: a percent `width` in a Chrome oracle depends on the headless viewport (780 not 900) - use px widths for oracles.
## 2026-11-19 — Bare text in a `<div>` takes the Draw IR text lane (Chrome 159)

- **Symptom:** `<div style="position:absolute;left:20px;top:30px">text</div>` painted grayscale glyphs one px right of Chrome's run and one row lower. Reported for an absolutely positioned box; a static or fixed `<div>` did the same. Chrome writes byte-identical PNGs for the bare text, the text in a `<span>` and the text in a `<p>`.
- **Root cause** (`_simple_web_engine2d_text_document`, `simple_web_engine2d_renderer.spl`): the lane router asked for a tag (`<p`, `<h1-3`, `<button`, `<span`, `<small`, `<code`, `<label`, `<a `). A page with none took the raster lane (`simple_web_layout_render_html_pixels`): 1-bit-looking grayscale text, no LCD, whole-pixel pens. Layout was never wrong: the box and the line breaks were Chrome's on both lanes.
- **Fix:** `_simple_web_engine2d_has_flow_text` finds character data in the body outside tags (not `style`, `script`, `title`, `textarea`, `select`). Such a page takes the Draw IR lane; if that lane discards the frame (skipped commands) it keeps the raster frame it had.
- **Held back:** the Draw IR lane ignores `letter-spacing`, `word-spacing` and `text-shadow` (a `<p>` page paints the same pixels with and without them), the raster lane paints them. A bare-text page that authors one stays on the raster lane (`_simple_web_engine2d_raster_only_text_property`). Bug: `doc/08_tracking/bug/draw_ir_text_lane_ignores_letter_word_spacing_text_shadow_2026-11-19.md`. Delete the hold when Draw IR paints them.
- **Chrome 159 / base / head** (400x120, `font:16px Liberation Sans`, `Hamburgefonstiv Qy`; ink bbox, LCD fringe pixels, pixels with a channel more than 8 from Chrome):

  | page | Chrome | base | head |
  |---|---|---|---|
  | absolute, bare | 21,32..165,46, 970 | 22,32..166,47, 0, 1236 | 21,32..165,46, 934, 357 |
  | static, bare | 21,32..165,46, 970 | 22,32..166,47, 0, 1236 | 21,32..165,46, 934, 357 |
  | absolute `width:90px`, bare | 20,32..140,64, 965 | 21,32..141,65, 0, 1253 | 20,32..140,64, 924, 357 |
  | absolute in a 60 px relative box | 35,42..155,74, 965 | 36,42..156,75, 0, 1253 | 35,42..155,74, 924, 357 |
  | fixed, bare | 21,32..165,46, 0 | 22,32..166,47, 0, 1086 | 21,32..165,46, 934, 1084 |
  | absolute, `<span>` (unchanged) | 21,32..165,46, 970 | 21,32..165,46, 934, 357 | same |

- **Re-pins, all toward Chrome** (8 px pages of `browser_renderer_spec.spl`, 96x32; they pinned the raster lane's exact-colour pixels, Chrome has none at 8 px because the run is LCD): non-white pixels Chrome / base / head: `text-transform` 416 / 228 / 411; `text-decoration-color` 311 / 191 / 309 with exact `#2563eb` 0 / 143 / 0; ltr `ABC` 86 / 51 / 83; rtl 87 / 49 / 81; clipped 233 / 114 / 231; ellipsis 177 / 68 / 131. Mismatch against Chrome base -> head: 454 -> 163, 289 -> 181, 94 -> 54, 94 -> 83, 251 -> 101, 184 -> 108. `simple_web_engine2d_renderer_spec.spl` bare `Simple Web` on `#123456` (120x40): off-background pixels 608 / 433 / 577, exact black 4 / 55 / 3, mismatch 596 -> 62.
- **More re-pins toward Chrome** (non-white pixels Chrome / base / head, mismatch base -> head): `test/feature/web_platform/css/pseudo_text_wpt_spec.spl`, 80x60, 8 px: ellipsis 165 / 58 / 90 against untruncated 411 / 200 / 402 (169 -> 113, 435 -> 176); `word-break:break-all` 546 / 287 / 537, second line on rows 10..15 with 35 pixels on row 14 (617 -> 238); `overflow-wrap:break-word` 549 / 287 / 541 (605 -> 198); `text-align:center` 65 / 38 / 61 (69 -> 62); `text-align:right` 65 / 38 / 57 (70 -> 13). `web_engine2d_gpu_offload_parity_spec.spl` bare `Simple Web` at 80x60, first line: 361 / 255 / 343.
- **LCD blend with a translucent text colour** (`engine2d_lcd_s32_tables`, `engine2d/helpers/lcd_s32_tables.spl`; shared by the CPU composite and the Vulkan kernel): the 5-bit coverage was scaled by alpha BEFORE the 31 -> 32 upscale, so `rgba(0,0,0,.5)` at full coverage was s = 17 and painted #777777 over white. Chrome 159 paints #7f7f7f: upscale first, then `* (alpha + 1) >> 8`, s = 16. Opaque text is the same table. It surfaced because `css_transparent_color_chrome159_spec` AC-7 renders a bare-text page, which now takes the LCD lane (darkest channel Chrome 127 / raster lane 127 / LCD lane before 119 / after 127). The same spec's AC-2 and AC-8 fail on base and pass on head.
- **Cost:** a bare-text page now pays the Draw IR lane: 8.9 / 9.6 s -> 11.3 / 11.8 s wall, the same as the `<p>` page (11.4 / 11.5 s on base); peak RSS 729 / 739 MB -> 732 / 739 MB. Catalog pages all carry a text tag and do not reach the new scan: 1x rows unchanged on all 8 pages; the dpr4 driver calls `simple_web_layout_render_html_pixels_engine2d_at_device_scale` directly and never went through the router.
- **Trap:** a spec that compares a plain bare-text page with a `letter-spacing` / `word-spacing` / `text-shadow` one now compares two lanes. Give the plain page the initial value (`letter-spacing: 0px`) so both stay on the raster lane.
- **Still open, measured here** (`doc/08_tracking/bug/inline_span_never_wraps_and_fixed_text_is_lcd_2026-11-19.md`): a `<span>` wider than its line never wraps (Chrome two lines, here one, 618 mismatching pixels against 357 for a `<p>`); Chrome draws `position:fixed` text without an opaque background in grayscale, here LCD (1084 against 356 with `background:#fff`).
- **Spec:** `test/01_unit/browser_engine/abspos_bare_text_chrome159_spec.spl` (8 examples, 0 / 7 on base before AC-8 was added, 8 / 8 on head).

## Fixed-position text is grayscale without an opaque background (2026-11-19)

- Chrome 159 (fringe pixels, red/blue differing by more than 16, 400x120): `position:fixed` with no background, `rgba(255,255,255,.5)` or `#fff0` is grayscale (0); `background:#fff` on the box, an opaque `<span>`/`<div>` background between text and box, `position:absolute` and `position:sticky` are LCD (970).
- Rule: the Draw IR text command carries `text-lcd:0` when walking from the text node up reaches a `position:fixed` ancestor before any element with alpha-255 `bg` (`_html_draw_ir_fixed_gray_text`, `simple_web_html_layout_renderer_paint_draw_ir.spl`); `draw_ir_adv.spl` sets Engine2D LCD per text command from it.
- Spec: `test/01_unit/browser_engine/fixed_position_grayscale_text_chrome159_spec.spl` (5 examples, 3 / 5 on base, 5 / 5 on head). Gradient backgrounds are not treated as opaque; not measured.
## 2026-11-19: Draw IR honours letter-spacing and word-spacing

- **Change:** `_html_draw_ir_resolved_text_command` (`simple_web_html_layout_renderer_paint_draw_ir.spl`) adds `letter_spacing_px` to every codepoint advance and `word_spacing_px` to each U+0020, and the run width, before the advances go on the wire (layout already folded the same values, so wrapping agreed). The routing hold `_simple_web_engine2d_raster_only_text_property` now lists only `text-shadow`.
- **Chrome 159 measured** (16px Liberation Sans, `Hamburgefonstiv`, 15 chars): `letter-spacing:2px` Range width 150.953125 (+30), `0.1em` 144.953125 (+24, i.e. 1.6px/char), `-1px` 105.953125 (-15), no spacing 120.953125; `a b c d` 48.03125, `word-spacing:10px` 78.03125 (+30 on 3 spaces); the last character's trailing spacing counts toward width. Wrap: `abcdef abcdef abcdef` in 110px is 2 lines, 3 lines with `letter-spacing:3px`.
- **Trap fixed:** `letter-spacing:-1px` was parsed with `parse_int` (sign dropped, +1) and `0.1em` as 0; `_decl_signed_spacing_px` reads sign and em.
- **Still open:** spacing is whole px (`Style.letter_spacing_px: i32`), so `0.1em` floors to 1px (ink x1 154 vs Chrome 163) and `-1px` is 1px off (125 vs 126); needs a milli field. A shaped run's `glyph_run` does not carry spacing. text-shadow unchanged.
- **Spec:** `test/01_unit/browser_engine/drawir_letter_word_spacing_chrome159_spec.spl` (6 examples; 1 / 6 on base, 6 / 6 on head). `abspos_bare_text_chrome159_spec` AC-8 re-pinned: letter-spacing now Draw IR, text-shadow still raster.

## 2026-11-19: fractional letter-spacing / word-spacing

- **Change:** `Style.letter_spacing_milli` / `word_spacing_milli` (i32, `0.1em` at 16px = 1600) are parsed by `_decl_signed_spacing_milli`; the `_px` fields stay as the truncation for the raster lane. `spaced_advances_milli` (`simple_web_html_layout_renderer_foundation.spl`) folds spacing into per-codepoint advances as differences of the ROUNDED cumulative pen, shared by layout (`core.spl`) and the Draw IR composer, so run width = round(natural + n x spacing) (Chrome 144.953125 -> 145) and wrapping agrees.
- **Pens:** Draw IR advances stay whole px on the wire. The exact spacing rides as `letter-spacing-milli` / `word-spacing-milli` props (device-scaled) to `FontRenderer._lcd_apply_pen_phases`, which adds it to the exact pen and takes the staged pen from the running sum of `advance_widths`, so each glyph gets its quarter phase and the ink matches Chrome.
- **Trap:** a negative letter-spacing pulls the box end in past the last glyph's ink; the horizontal band clip in `draw_ir_adv.spl` is widened by that overhang (`-1px` was clipped to 125, Chrome 126).
- **Chrome 159 measured (ink x1):** `0.1em` 163, `-1px` 126, `0.5px` 147, `word-spacing:2.5px` 74; `0.1em` wrap at w120 = 3 lines (20,32..76,79), w130 = 2 lines (..139,61).
- **Spec:** `drawir_letter_word_spacing_chrome159_spec` 8 examples (AC-7/8 new; AC-3/4 re-pinned to Chrome).

## Shaped-run letter/word-spacing (2026-11-19)

- **Which text is shaped:** only Arabic/Devanagari (`_resolved_font_complex_script`) with a `lang` the font registry maps to an accepted bundled face. `lang="ar"` -> Noto Sans Arabic gives `glyph_run.valid`; `lang="hi"` currently does NOT (unshaped fallback, width 103 vs Chrome 73). Latin ligatures/kerning never take this path.
- **Chrome 159 rule (measured, Range widths):** letter-spacing is added after every unit except Arabic-script letters (joined or isolated); spaces, digits and Latin in the run take it. `مرحبا بالعالم` 77.09 -> 79.09 at 2px, `م ر ح` +4, `مرحبا abc` +8. Devanagari spaces per grapheme cluster (+16 for 8 clusters).
- **Change:** `spaced_advances_milli` skips the letter gap for `Script.Arabic`. Engine2D paints shaped runs from the command advances, so the glyph run needed no edit.
- **Trap:** ink bbox y/x0 for Arabic differ from Chrome on base (font raster/line box), so the spec pins width (`cmd.width`) and ink x1/x0 DELTAS vs the unspaced render, not absolute ink boxes.
- **Spec:** `shaped_run_spacing_chrome159_spec` 6 examples.
## 2026-11-19: empty inline opens no line box

- **Change:** `inline_subtree_is_empty` (layout_engine.spl) classifies an inline child; the block child loop tracks `inline_run_has_content` and skips the line-box cursor advance when a run is all empty inlines / collapsible whitespace (CSS 2.1 9.4.2). A 0-height block then self-collapses, so 20px margins collapse through `<div><span></span></div>`.
- **Chrome 159 measured (div height):** `<span></span>` 0, `<span> </span>` 0, `<b></b><i></i>` 0, `padding-left:4px` span 18, `border-left:1px` span 18, `<span>x</span>` 18; `p{margin:20px 0}` + empty div + `p`: second p top = first bottom + 20.
- **Content test:** text, `br`, replaced/atomic box, non-zero horizontal margin/padding/border (nonzero vertical-only padding still counts as empty, unmeasured).
- **Spec:** `empty_inline_line_box_chrome159_spec` (7 examples; 3 / 7 on base, 7 / 7 on head).
## 2026-11-19: Draw IR sharp `text-shadow`

- **Change:** `Style.text_shadow_raw` keeps the cascaded value (inherited like the other text-shadow fields). `_html_draw_ir_text_shadow_commands` (`simple_web_html_layout_renderer_paint_layout.spl`) parses it with `parse_box_shadow_layers` and, for each blur-0 layer, pushes a copy of the `#text` run (and of each wrapped line) BEFORE the run, in the layer colour at the layer offset (x device scale). Layers go last-to-first so the FIRST listed ends up on top.
- **Chrome 159 measured** (16px Liberation Sans, `Hamburgefonstiv Qy`, abspos at 20,30): shadow glyphs are LCD like the text (`color:transparent;text-shadow:2px 2px black` fringe 970 = plain text 970); a BLURRED shadow (`0 0 3px black`) is grayscale (fringe 0 on a transparent-text page). Ink bboxes: `2px 2px red` 20,32-167,48 (red 442 px); `-2px -1px red` 18,31-166,46 (486); `1px 1px red, 3px 3px blue` 20,32-169,49 (red 184, blue 275); `0 0 3px black` 18,29-168,49.
- **Routing:** `_simple_web_engine2d_raster_only_text_property` now holds only a BLURRED (or unparsable) text-shadow on the raster lane. The raster lane does not paint the blur either (ink 839 px vs Chrome 2466), so blur is a known gap: it needs a glyph blur primitive (Gaussian on the glyph mask, sigma = blur/2), not yet in Engine2D.
- **Trap:** the shadow bbox x1 is 1px short of Chrome for the same reason plain text is (166 vs 165); pin it within 1px.
- **Spec:** `drawir_text_shadow_chrome159_spec` (5 examples, 0 / 5 on base, 5 / 5 on head); `abspos_bare_text_chrome159_spec` AC-8 re-pinned (sharp shadow -> Draw IR, blurred -> raster).

- Double borders (2026-11-18): stripe = `(w+1)/3`; uniform-width double = two solid rings (outer on border box, inner inset `w-stripe`, radii `max(r-inset,0)`). Draw IR `<id>_d0`/`_d1`, raster via `fb_border_ring_per_corner_clip`. Engine2D sends all rounded borders to the typed ring. Pinned by `border_double_radius_chrome159_spec`.

- Raster outline over text (2026-11-19): deferred in-flow outlines that no positioned box overlaps paint after pass 6 (Chrome paints them over later in-flow text); overlapped ones keep the pre-pass-2 flush. Pinned by `outline_over_text_chrome159_spec`.

- `<img>` natural size (2026-11-18): layout reads the supplied resources (`layout_set_images` around `web_html_layout_tree`); auto sides take the natural size or follow the aspect ratio of the given side (`img_resource_auto_outer_w/h`). Pinned by `img_natural_size_chrome159_spec`.

- Dash layout (2026-11-19): `border_dash_runs` gives Chrome's dash runs on a straight side: dash 2t (dotted t), nominal gap t fitted by SelectBestDashGap so both ends are full dashes; L <= 2·dash is solid, 2·dash < L < 2·dash+gap scales two dashes and the gap together. Raster and Draw IR share it. Pinned by `border_dash_layout_chrome159_spec`.

- Opacity groups (2026-11-19): `_simple_web_opacity_root_bounds` counts a box-shadow as a paint item (bg + shadow at 0.5 is a group, `ff7e7e`), matching the raster's `_raster_group_node_ops`. Pinned by `opacity_multi_root_chrome159_spec`.

- Round dots (2026-11-19): `dotted` dots are the circle inscribed in each t x t dash cell (`border_dot_row_spans`, pixel-centre test), on raster and Draw IR. Capture Chrome oracles at 400x300: small headless windows can leave rows unpainted. Pinned by `border_dotted_round_chrome159_spec`.
- Inline span wrap (2026-11-19): a plain inline element (`inline_box_is_plain_element`) that OPENS its line (`inline_x == inline_start_x`) and is wider than it has its box width clamped to the line in the block line loop (layout_engine.spl, before the `text-align` sole-#text block), so its nested #text run wraps (Chrome 159, 120 px: `<span>alpha beta gamma delta</span>` h=36, nested `<b>` too, nowrap h=18). Before, only a `#text` child was clamped, so the span laid out at intrinsic width and overflowed. **Trap / remaining gap:** a span that starts MID-line and is longer than the remainder (`one <span>alpha ... zeta</span> two`, Chrome 3 fragments, h=54) still lays out as a block of line width (h=36): needs the `text_first_dx` first-line inset applied through the span's text child. Per-fragment background/padding is not supported (background paints one rect). Spec: `inline_span_wrap_chrome159_spec`.

- Rounded dashes (2026-11-19): a uniform dashed/dotted border on a rounded box is ONE closed centre-line path from the top-left arc end, clockwise, gap fitted by SelectBestDashGap closed (n gaps for n dashes) -> `border_rounded_dash_spans`, shared by raster and Draw IR. Prove a paint rule in a Python model against every uniform Chrome cell before porting (7505/7505 here). Pinned by `border_dashed_rounded_chrome159_spec`.
- Rounded mixed sides (2026-11-19): same closed dash path, each pixel coloured by its nearest side (diagonal split, ties to the vertical side), solid sides fill their ring part. On Draw IR the box command must paint NONE of such a border's sides (`_html_draw_ir_rounded_dash_box` zeroes its widths), or its solid corners cover the dash gaps. Pinned by `border_rounded_mixed_sides_chrome159_spec`.
- Rounded per-corner dashes (2026-11-19): same closed path, each corner's arc radius r - t/2, straight pieces between the radii; matches Chrome only when every r >= t (r < t corners join differently). Pinned by `border_rounded_per_corner_dash_chrome159_spec`.
- Small dash corners (2026-11-19, measured, unfixed): a single corner with r < t keeps the closed path (first top dash at x = max(r, t/2)); errors stay local and vanish at r >= t-1. When r < t/2, the leg after the corner is painted only on its inner half, with a diagonal join. Several small corners switch the top side to a per-side layout. Tables are in the round-4 bug record.
- Custom-property tables (2026-11-19): the theme sheet has 469 `:root` selectors and about 500 properties. `_css_collect_custom_props`, `_css_collect_scoped_custom_props` and `CssVarResolutionState` now grow with the sheet; the old 200/400 caps silently dropped late `:root` blocks. Trace with `SIMPLE_WEB_STYLE_TRACE=1` (`css-var-unresolved count=`). Trap: in a Simple string, `{--a:x}` is interpolation, so write `{{--a:x}}` in spec CSS.
- Corner AA (2026-11-19): Chrome's corner AA is Skia CPU scanline AAA (diagonal-asymmetric, GPU == --disable-gpu); no coverage formula fits, and a port of Skia's flattening + AAA is required. Check diagonal symmetry before fitting any AA model.

- Raster opacity group layer alpha (2026-11-19): B/W two-pass alpha is exact only for one non-opaque paint per pixel; where paints overlap, paint a third pass over opaque black with all member colours (and image pixels) forced to white at their alpha and read its channel as the layer alpha (`_raster_white_alpha_pass`). Pinned by `opacity_group_chrome159_spec` raster rows.
- `<img>` opacity (2026-11-19): even a lone `<img>` with opacity is a one-member layer in Chrome; composite its pixels with `css_opacity_group_composite_pixel`, never fold opacity into the pixel alpha (one level off). Pinned by `img_opacity_chrome159_spec`.

- Vulkan gray text (2026-11-19): `font_atlas_batch.comp` gray branch = `color.spl` `blend()` image rule (div255r), the `_glsl_blit` twin; regenerate with `glslangValidator -V` + `scripts/tool/spirv-to-spl-words.shs`, split head/tail halves, and pass `check-font-atlas-batch-spirv-pinned.shs`. Metal/CUDA/legacy strings in `common/gpu/font_atlas_composite.spl` still use the old flooring rule.

- Thin dashes (2026-11-19): Blink's dash length depends on DEVICE thickness: t < 3 dash 3t / gap 2t, t >= 3 dash 2t / gap t (measured at 1x: 1px `###..`, 2px `######....`, 3px `######...`, 4px `########....`; at dpr4 a 1px border is 4 device px and uses the thick 8/4). `border_dash_runs` switches ratio on t (raster and Draw IR share it); dotted unchanged. The dash-layout spec's old 1px/2px pins came from a dpr4 render but ran at 1x; they are re-pinned from 1x Chrome, and 1x partial-coverage pixels (`?`) are not pinned. The ratio keys on device thickness: `border_dash_runs(.., device_k)` (Draw IR passes `layout_device_scale()`, raster 1).
- Square dots at 1x (2026-11-19): Chrome 159 draws 2px/3px `dotted` as SQUARE pixel runs on an integer pitch 2t, not fitted fractional dots: n = (L - t + 2) / 2t + 1, interior gaps exactly t, leftover e = L - t - 2t(n-1) goes to the end gaps (first end first, <= 1px each); 3px e=3 grows both end dots to 4px. Same on top/bottom/left/right. 4px/5px stay fitted + AA (fractional centres, e.g. 4px L=200 pitch 7.84). `border_dash_runs` -> `_border_square_dot_runs` for dotted, t in {2,3}, device_k 1 only. Measure many lengths (50..89), not one 200px box: a single length hid the pitch-2t rule. Pinned by `border_dash_layout_chrome159_spec` (1x dotted). 1px (2026-11-19, measured sides 50..60/100/200, full-black, not AA): pitch 2, n = (L+1)/2, flush at the last px; an even L widens the FIRST dot to 2px (`##.#.#`), odd L is plain `#.#.#`; the t=2/3 formula over-counts for t=1, so `_border_square_dot_runs` has a separate t == 1 branch.
- Typed border ring vs the transient cap (2026-11-19): #10343 routed every rounded border through `engine2d_draw_ir_render_typed_border_ring`, whose `engine2d_draw_ir_mask_geometry_safe` area cap (16.7M px) dropped the whole ring for a page-long box at dpr4 (css-layout section 3408 x >4900 device px: border vanished, 3.25 -> 3.74). The ring allocates only its strips, so only the whole-box fallback keeps the area cap; `border_ring_taller_than_cap_spec`.
- Auto-table column split in milli-px (2026-11-19): Chrome shares a table's slack in proportion to FRACTIONAL max-content widths (bold "Feature" 57.797, "Expected" 71.141) and rounds only the cumulative column edges. `explicit_auto_table_column_offsets` now keeps a per-column milli remainder (`col_frac`, from `table_cell_text_frac_milli`: `resolved_font_width_milli - resolved_font_width * 1000` of a cell whose ONLY child is one text run; every other cell stays whole-px) and calls `table_distribute_auto_columns` with min/max/available scaled x1000, then edges `(cum_milli + 500) / 1000`. The distributor's interpolation product is i64 now (milli widths overflow i32). Measured via getBoundingClientRect + screenshot rules (810px table at x=45: columns 377.297/431.703, rules 45/422/854; Base put the middle rule at 423). Pins `table_auto_milli_column_split_chrome159_spec` (3 pages); side effect: the plain UA table's third cell is 19 wide (Chrome snaps 45.6..65.4 to 46..65), re-pinned in `table_ua_cell_padding_and_spacing_spec`. Trap: a table at x=0 or a width where the integer split already rounds right does NOT reproduce it, so the spec needs the fractional left offset (45px wrapper). Cells with inline children (`<code>`) keep the integer width (not carried).

## Trap: `animation` page flipped 2.33/2.40 = Chrome `--virtual-time-budget` vs media controls (2026-11-19)
The Chrome capture, not Simple, varied. Simple PPMs and a fixed Chrome state were byte-identical across runs; Chrome PNGs alternated between two states ~5% of runs (2/40, 2/12 with `--virtual-time-budget=3000`), differing in one 404x48 box at (304,280): the `<audio controls>` shadow UI, either fully laid out (play, 0:00 / 0:00, volume) or collapsed to the slider (8.5k px, which is the 2.33 vs 2.39 gap). Under virtual time the media-controls ResizeObserver layout lands at a racy virtual instant. `--run-all-compositor-stages-before-draw` and `--mute-audio` do not help (3/150, 1/40). Dropping the budget from the CAPTURE gave 150/150 identical (catalog pages have no scripts/timers). The viewport probe keeps the budget (its script is synchronous). Do not add the flag back; to detect this class capture a page 40x and `md5sum`.
- 2026-11-19 `backend_emu_adv.spl` `emu_draw_shadow_rect`: zone clamps run in order (0 <= nz0 <= i0 <= i1 <= nz1 <= rw). A blur wide for its box (no fully covered column) cut by the frame's right edge left an interior run past the row end — wrong pixels, or an index-out-of-bounds on the last row. `box_shadow_frame_clip_spec` crash -> green. Trap: clamp the outer zone first, then the inner one inside it.

## 2026-11-19 layout census: html / css-layout / overview (no layout offsets)

At 1x, all 97 mismatch clusters on html (1.78), css-layout (2.13) and overview (1.13) have
equal Chrome/Simple ink boxes (+-1px heading-top deltas = fractional font y-raster); +-3px
shift search gains nothing in any cluster. Remaining residual is glyph raster, not layout.
Tables and method: `doc/08_tracking/bug/web_render_layout_census_html_css_layout_overview_2026-11-19.md`.

- 2026-11-19 `backend_emu_adv.spl` `emu_draw_shadow_rect`: shadow writes keep the destination alpha (`dst & 0xFF000000`); they wrote alpha 0, so a translucent box over its own shadow composited onto "transparent" and turned opaque white (cpu_simd `FFFFFF` vs Chrome `C3C3C7`). `box_shadow_keeps_dest_alpha_spec` red -> green. Open: Draw IR outer shadow has no knockout under the box; inside a transparent offscreen the shadow stays alpha 0 (needs src-over alpha).
- 2026-11-19 `paint_draw_ir.spl` producer: a typed linear gradient (raw list cleared by the typed projection) on a rounded box is emitted as one `BackgroundGradientLayer` (`linear_gradient_line_q10_at_angle` over the origin box, tiled on it, repeating) plus `background-gradient-layer-clip-radii`, so the rounded layer branch paints and clips it; Draw IR used to paint the box colour only. `rounded_typed_gradient_chrome159_spec` cpu_simd/Vulkan red -> green. Trap: the tile must be the origin box and repeat, or the gradient clamps under a transparent border (Chrome repeats it). Open: raster leaves the border area at the box colour.

- 2026-11-19 `shaders/shadow_rect.comp`: the Vulkan shadow kernel keeps the destination alpha like its CPU twin (it mirrored the old alpha-0 packing). Regenerate with `scripts/tool/gen-shadow-rect-spirv.shs`; `check-shadow-rect-spirv-pinned.shs` guards the blob. Trap: a one-instruction shader edit rewrites most SPIR-V words (offsets shift); prove reproducibility by regenerating the unchanged shader.
- 2026-11-19 outer box-shadow knockout (CSS Backgrounds 3 section 7.1): raster `_paint_box_shadow_outside_box` and Draw IR `_engine2d_draw_ir_render_box` restore the pre-shadow pixels inside the rounded border box when the box colour is not opaque (Draw IR: readback before/after + `draw_image`, gated by `engine2d_draw_ir_has_outer_shadow`). `box_shadow_knockout_chrome159_spec` 0/3 -> 3/3. Trap: unit tests of `paint_box_shadow` probe inside a transparent box, so the knockout lives at the call sites, not in the painter. Open: GPU readback sync on gated boxes. The binary edge was fixed 2026-11-19 (knockout AA edge, below).
- 2026-11-19 raster `fb_style_background_opacity_clip`: a repeating background tiles from the first tile edge at or before the clip box, not from the positioning origin. A transparent border used to leave the border strip unpainted. Pinned by the raster border/padding case in `rounded_typed_gradient_chrome159_spec`.

- 2026-11-19 shadow inside an `opacity` group: `emu_draw_shadow_rect` (`_emu_shadow_px`) and `shaders/shadow_rect.comp` use Chrome src-over for a non-opaque destination (the group's transparent offscreen). They used to mix with the destination RGB and keep alpha 0, so the shadow vanished. Opaque destinations keep the twin integer formula. Pinned by `box_shadow_opacity_group_chrome159_spec` (cpu_simd + Vulkan).

- 2026-11-19 `backdrop-filter: blur()`: Chrome 159 blurs only the backdrop inside the border box, mirrors the box edge, clips to the rounded box, and uses Skia's SVG triple box (sigma >= 2, 8-bit premultiplied; it matches Chrome exactly where a true Gaussian is up to 8 levels off at k=1). Shared kernel `engine2d_backdrop_blur_pixels`; Draw IR reads `backdrop-filter-blur-milli` (device-scaled) in `_engine2d_draw_ir_render_box` before shadows; raster `_paint_backdrop_blur`. Pinned by `backdrop_filter_blur_chrome159_spec` (raster k=1, cpu_simd + Vulkan k=4). Other filter functions are still ignored.
- 2026-11-19 raster `fb_soft_box_shadow`: the shadow's rect mask is blurred with Skia's triple box (sigma = blur / 2) as one `engine2d_blur_step_profile` per axis, over about 3 sigma. The old pixel-edge erf product stopped at 1 x blur and was up to 11 levels dark. Pinned by `box_shadow_raster_falloff_chrome159_spec` (k=1).
- 2026-11-19 Draw IR shadow at 1x: `_emu_shadow_profile` (CPU twin and the Vulkan host-built profiles) now uses `engine2d_blur_step_profile`, shared with the raster, from leaf `engine2d/helpers/blur_kernel.spl` (`draw_ir_box_effects` imports `engine`, so a backend cannot import it directly). Coverage rounding is `(+127)/255` in the twin and in `shadow_rect.comp`; regenerate with `scripts/tool/gen-shadow-rect-spirv.shs`. `box_shadow_raster_falloff_chrome159_spec` covers all three lanes at k=1.

- 2026-11-19 `backdrop-filter` colour functions: Filter Effects 1 sRGB matrices in order, clamped after each (grayscale/sepia use 0.2126, saturate/hue-rotate 0.213), composited over the unfiltered backdrop, with blur first. Helpers `engine2d_backdrop_color_matrices` / `engine2d_backdrop_color_filter_pixels`; pinned by `backdrop_filter_color_functions_chrome159_spec`.
- 2026-11-19 knockout AA edge: `engine2d_draw_ir_shadow_knockout_pixels` and raster `_restore_inside_box` mix corner-band pixels by `rounded_rect_coverage256` (shared `engine2d_mix256`), so the shadow bleeds into the box edge as in Chrome; `backdrop-filter` writes back through the same two, so its clip is anti-aliased too. Trap: pin the shadow's share (with minus without), not the absolute pixel; our rounded-corner coverage is still up to 16 levels off Chrome, which is asymmetric in x/y (open bug). `box_shadow_knockout_aa_edge_chrome159_spec` 0/3 -> 3/3.
- 2026-11-19 readback cost: a Vulkan knockout or backdrop box pays two region reads, and each is a full-frame download (4.6 s at 1200x720 by default, 0.14 s with `SIMPLE_VK_READBACK=native`) plus a crop. The crop is now one span per row (`RenderBackend.read_pixels_region`). Trap: measure Vulkan web perf with and without `SIMPLE_VK_READBACK=native`, or the interpreted unpack hides every other cost.
- 2026-11-20 button content centring: Chrome centres a `<button>`'s content box vertically (taller content keeps the top); `button_content_centre_pass` runs after layout in `web_html_layout_tree` and in the `layout_selected` contain fast path (idempotent). Trap: pin it with a font-free inline-block (`font-size:0; line-height:0`) so text metrics cannot hide or fake the offset.
- 2026-11-20 Backdrop Root (Filter Effects 2): an opacity-100 element with `backdrop-filter` and a backdrop-filtered descendant becomes an opacity group (`_simple_web_backdrop_root_flags`); its own backdrop is split out and painted in the parent before the group (`_simple_web_backdrop_root_split`), and a backdrop over non-opaque layer pixels draws src-over (`_engine2d_draw_ir_render_box`). Chrome nested white glass 250 vs 239 without the root. Trap: an all-white fixture cannot catch a colour-pass alpha bug, so pin a tinted inner panel too (124,181,251). Trap: `vulkan_device_blur_rect_count` stays 0 for CSS `backdrop-filter`, because the blur is host-side over a readback; assert readbacks, never device blur. Raster: a Backdrop Root is a white-alpha group whose alpha pass records each nested filtered alpha and whose colour pass replays it for a premultiplied src-over (`_raster_bdr_mode`); trap: the black/white recovery alone cannot express it (235 vs Chrome 249 premultiplied). Groups with text on a non-opaque root or shadows are not admitted (window fixture unchanged at 555‰).
- 2026-11-19 flex column `min-height: <n>vh`: `col_flex_target_heights` takes the resolved minimum (the style keeps `vh` only as the `min_height_vh` flag, so reading `min_height_px` alone dropped it). `flex_column_min_height_vh_chrome159_spec` 0/3 -> 3/3. Trap: a length stored as a unit flag needs resolving at every reader.
- 2026-11-19 `.widget-panel` fill: layout fills a `widget-panel` to the viewport bottom only in legacy widget chrome (no `<style>`), read from `#root.legacy_widget_chrome` because `<style>` nodes are dropped at parse. Taskbar Vulkan agreement 364 -> 674‰. Trap: a class-name hack in layout must use the same legacy test paint uses, or CSS pages lose their CSS boxes.
- 2026-11-20 Backdrop Root, viewport-sized groups and colour functions: a CSS group whose bounds clamp to the viewport (a big `box-shadow` halo) used to hit `fills_target_exactly` in `_engine2d_draw_ir_render_batch_embedded` and paint unisolated. A nested `saturate()` over the transparent group composited src-over twice (once in `engine2d_backdrop_color_filter_pixels`, once at `draw_image_blend`). Both fixed in `draw_ir_adv.spl`; window fixture Engine2D 556 -> 933‰, raster still 555 (not admitted). Trap: a correct Draw IR dump does not prove the paint isolates the group. Bisect with Chrome pages that add one feature at a time (halo, border, overflow, text, saturate).
- 2026-11-20 raster repeating-background tiles: `fb_style_background_opacity_clip` clips every tile to the background painting area. The repeat grid starts a whole tile left of / above a bordered box, and the ancestor clip alone let those tiles cover neighbours (the taskbar's running panel painted over the pinned buttons). `background_repeat_tile_clip_chrome159_spec` 0/2 -> 2/2; taskbar button pixel now equals Chrome. Trap: a painter that over-draws outside its box is invisible to "which painter covers pixel P" logging; track the pixel value per node instead.
- 2026-11-20 `background-color` after `background`: the shorthand now always applies, and a later `background-color` overrides only the colour (it used to zero the shorthand's gradient). `background_color_after_shorthand_chrome159_spec` 0/2 -> 2/2. Trap: "the last declaration wins" is per longhand; a shorthand-vs-longhand order test must not pick one whole branch.
- 2026-11-20 `::before`/`::after`: generated nodes are APPENDED after the parsed arena (index = structural_id - 1 never shifts); `build_child_index` links `::before` first, and only paint order / hit ties / raster pass 2 walk `html_tree_order`. Trap: a generated box at the arena tail paints after every real box in any index-order pass. The fixed overlay covered the later relative `.app` on raster (window 555 -> 540‰) until pass 2 walked tree order (-> 587‰).
- 2026-11-20 raster overlap rule vs generated boxes: `_raster_opacity_groups` used ARENA index as paint order, but `::before`/`::after` live after the parsed arena, so the window fixture's `body::before/::after{position:fixed;inset:0;z-index:0}` "painted over" the glass and dropped its Backdrop Root (raster window 932 -> 587 permille). Fix: rank by `html_tree_order` when the page has generated content, and skip boxes in a lower root stacking layer (`_raster_root_layer_z`). Trap: any arena-index ordering is wrong once generated boxes exist. Evidence: `backdrop_root_glass_raster_window_shape_content_chrome159_spec` 3/4 -> 5/5; raster window 960 permille. Open: raster still paints a later z-0 generated box over z-1 content outside the group.
## 2026-11-19 — fractional font sizes: hint knots at the float size

- **Cause** (`src/lib/common/encoding/sfnt_glyf.spl`, `_lcd_hint_knots`): the y hint knots were built from the whole `size_px`, so 13.3333 px (UA textarea/`<small>` mono) drew 9-row caps where Chrome draws 10, and 21.3333 px sans started one row low. FreeType's light autohinter scales at the float size; only the 6..14 ppem x-height round-up rule reads the whole ppem.
- **Fix:** `_lcd_hint_knots(…, size_milli)` scales at `size_milli / 1000`; the cache key carries `size_milli`. Whole sizes pass `size_px * 1000`, so their raster is byte-identical (bands 13/16/19 px unchanged).
- **Evidence:** forms-media 1x 2.16 -> 2.15, other 1x and all dpr4 rows unchanged. Spec `test/01_unit/browser_engine/fractional_font_y_raster_chrome159_spec.spl` pins first/last ink rows of 9 bands (fractional + whole) against Chrome on cpu_simd and vulkan.

## 2026-11-19 — row flex text items at exact (LayoutUnit) width

- **Cause** (`simple_web_html_layout_renderer_layout_engine.spl`, row flex auto-width branch): only a `<button>` item carried its fractional width (`form_control_button_frac_delta_milli_px`); every other auto-width item was sized at the whole-px rounding of its text, so the error accumulated along a row. Chrome keeps each item at its max-content width rounded UP to a LayoutUnit (1/64 px, `FromFloatCeil`; `HTML` 16px DejaVu Sans = 43.5547 exact -> 43.5625) and snaps only the edges. Measured: bordered 13px items ended at 110/215/254 vs Chrome 111/216/255, bold 14px padded items one px short from the second edge, `HTML`+`CSS Paint` ended at 118 vs 117.
- **Fix:** `flex_item_text_frac_delta_milli_px` (layout_foundation) gives an auto-width item whose content is ONE text run (whole-px font, unadjusted run, `intrinsic_w` = run + padding + border) its LayoutUnit-ceil remainder (`layout_unit_ceil_milli`); the existing edge-snap path places it. Truncated milli widths without the 1/64 ceil sum 6 items to 357.498 where Chrome has 357.5 -> one px short at the row end. The item's true width is handed to its layout (`item_frac_w_hand_over` -> `box_frac_w_take` -> `box_frac_w_at`) so its label fit test compares exact widths: `CSS Paint` (73.8125) stays on one line in its snapped 73 px box. With no hand-over the `<button>` 1 px slack still applies.
- **Trap:** an item WITHOUT its own remainder (an `<img>` after a fractional text item) must not take the snapped width: its `remaining_w` is the rest of the row, not its size (combo matrix tc-img-shrink0/as-center/order1 went 40 -> 282 px). Such items move only their left edge and keep their own laid-out width.
- **Not covered:** fractional font sizes (13.3333px) carry no `resolved_font_width_milli`, so such items keep whole-px widths (one px off in a 13.3333px `span` row).
- **Evidence:** `test/01_unit/browser_engine/flex_text_item_milli_edges_chrome159_spec.spl` (5 rows, Chrome runs pinned) red on base (3 rows), green on head.  Combo matrix PASS (81 mismatching, unchanged); 1x catalog html 1.78 -> 1.77, css-paint 2.38 -> 2.37, others equal.

## 2026-11-19 — fractional font sizes: exact text width at the 26.6 size

- **Cause:** `Style.resolved_font_width_milli` (read by the row-flex item remainder, the table auto-column split and the mid-line pen origin) was only set for whole-px sizes (`core.spl`: `st.font_size_milli == 0`), and `resolve_font_metrics_with_language_milli` never filled `width_milli`. 13.3333px / 10.6667px items therefore fell back to whole-px text widths: `Evidence` ended at 111 (Chrome 110), a bordered 10.6667px row at 146 (Chrome 147).
- **Chrome rule (measured):** FreeType gets the size in 26.6 fixed point, so advances scale at `floor(size*64)/64`: 10.6667 -> 10.65625, 13.3333 -> 13.328125, 21.3333 -> 21.328125. `v` (1024 units, Liberation Sans) is 341/64 px at 10.6667, not 342/64; `Overview` is 44.4219 (float-size model 44.4541). Whole sizes are multiples of 1/64, so they are unaffected. Chrome resolves sans-serif to an Arial-metric face here (`v` = 8.000 px at 16 px = 1024/2048 units; DejaVu would be 9.47) even though `fc-match sans-serif` names DejaVu Sans.
- **Fix:** the milli resolver reports the reference pen end rescaled to the 26.6 size (kept only when it rounds to the integer `width`); `core.spl` stores it, plus the space width at the same size, for fractional runs too.
- **Residual (not fixed):** regular 18.72px words measure 0.03..0.06 px under the 26.6 model in Chrome (`Overview` 77.953 vs 78.010), while single glyphs match. Cause unknown (not kerning: 16px shows none). The edges in the spec agree either way.
- **Residual (gate):** `advances`/`width` are still rescaled at the float size; only `width_milli` uses the 26.6 size, and it is dropped (-1, base behaviour) when it does not round to `width`. The size ratio is ~0.9990 at 10.6667 px and ~0.9996 at 13.3333 px (~0.05 px per 50 px, ~0.1 px per 300 px), so some runs still fall back and keep the old 1 px error. Paint and wrap are not on the 26.6 size either. Follow-up: rescale the pen boundaries at the 26.6 size too (done below, same day).
- **Spec:** `test/01_unit/browser_engine/fractional_font_size_text_width_chrome159_spec.spl` (flex 13.3333 / bold 18.72 / bordered 10.6667, collapsed table 13.3333; colour runs from a Chrome screenshot).

## 2026-11-19 — fractional font sizes: every advance at the 26.6 size

- **Cause** (`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`): `resolve_font_metrics_with_language_milli` rescaled the 8x reference boundaries by `size_milli / (ref * 1000)` (the float size), and `_lcd_apply_pen_phases` did the same for the paint pens. Chrome hands FreeType the size in 26.6 fixed point, truncated (`SkScalarToFDot6`): 10.6667 px is 682/64, 13.3333 px 853/64. A ~300 px 10.6667 px run came out up to 0.3 px wider than Chrome, so its box and its glyph ink ended 1 px right (3 of 6 long rows). #10491 had only fixed the run's `width_milli`, kept when its rounding agreed with these whole boundaries.
- **Fix:** one helper, `_fr_size_26_6(size_milli) = size_milli * 64 / 1000`; the layout boundaries, the exact width and the paint pens all scale by `s266 / (ref * 64)` through `_fr_scale_round`. The "kept only when rounding agrees" guard is gone: the run END is anchored to the exact pen end (`width = round(width_milli)`, the last advance absorbs the <= 1 px; `_lcd_apply_pen_phases` sets `whole[n]` the same way, so its `advance_widths` check still agrees). Without the anchor the 26.6 scale broke `Overview` at 13.3333 px: 433 ref px -> 55.49 (55) while the exact end is 55.5469 (56, Chrome), so the old guard dropped `width_milli` and the box lost a px. Line height is unchanged (still the float size). Whole sizes never reach this code (the resolver returns early on `size_milli % 1000 == 0`).
- **Evidence:** spec `test/01_unit/browser_engine/fractional_font_size_glyph_advance_chrome159_spec.spl` pins 11 box ends and 8 ink ends vs Chrome 159; base fails 3 + 3 rows, head passes.
- 2026-11-20 line-wrap fit (all font sizes): a line whose whole-px byte-advance sum EQUALS the available width is re-measured exactly (`wrap_back_off_exact`, 26.6 milli width rounded up to a LayoutUnit) and ends at its previous space when it overflows (Chrome breaks `The quick brown`, 117.39 px, in a 117 px box); a space at which the fit loop stops HANGS (`space_hangs`), so a phrase that fits only without its trailing space stays on the line. `line_wrap_layoutunit_fit_chrome159_spec` AC-1 red on base (odd bands 3 lines vs Chrome 2), 2/2 on head. Trap: only the `used == width` line can overflow, because whole-px sums are within 1 px of exact; measuring every line would cost a font resolve per line. Trap: shrink-to-fit boxes (float, inline-block) sized from one run still lay it on one line (AC-2 pins it), so the exact test needs no box LayoutUnit width there.

## 2026-11-20 — a plain inline element that starts mid-line wraps like its text run

- **Cause** (`simple_web_html_layout_renderer_layout_engine.spl`, inline run loop): only a bare `#text` that starts mid-line took the "run owns the line box, line 0 inset by `text_first_dx`" path; a `<span>`/`<b>`/`<a>` starting mid-line was laid out at its pen with its full advance width, so its text ran past a 200 px block to x=399 on one line and the content after it opened a new line. Paint drew the element's background as one rect over its whole box, covering the text before it.
- **Fix:** `inline_sole_text_run` (layout_foundation) picks the one `#text` child of a plain inline element with no horizontal margin/padding/border. The loop wraps that run exactly like a bare run: first word does not fit -> break before the element; otherwise the element's box becomes the line box and `g_text_first_line_dx_pending` carries the inset down to the inner `#text`, whose record now stores the inset it consumed (`run_first_dx`). Content after a wrapped element continues on its last line (the bare-run continuation, keyed on `run_node`). Paint: `_html_draw_ir_inline_fragment_boxes` (paint_draw_ir) replaces the element's box with one box per wrapped line, `bx[run] + text_line_box_dx` by the line's text width, the element's content-area tall, from the run's `by` + k * line-height. Also fixes a wrapping element that OPENS its line (its background was one 200 px strip).
- **Evidence:** `test/01_unit/browser_engine/inline_span_midline_wrap_chrome159_spec.spl` (span/b green backgrounds, black `<a>`, 200 px block, line-height 20; Chrome fragments `getClientRects`), red on base (25 fields), green on head; probes at line-height 30 and 13.3333 px match within 1 px.
- **Not covered:** an element with horizontal padding/border/margin or more than one child, nowrap/pre, centred/right/RTL lines, float-shortened lines, and the raster (`paint()`) lane.
- **Trap (pre-existing, not fixed):** text AFTER a bold/italic inline element is a few px off Chrome even on one line (`Lead <b>bold</b> tail text.` ink ends 128, Chrome 131; `abc <span>x</span> it.` 52 vs 49), so the spec's `<b>` band has no tail.

- 2026-11-20 raster Backdrop Root admission: the window fixture's glass was rejected by FIVE checks at once (root/panel/button shadows, text on a non-opaque root, the panel's `saturate`, `<button>` layer-safety), so lifting any subset left it at 555‰; probe every reject reason before fixing one. Backdrop roots now whiten `box_shadow_raw` colours (`_raster_white_shadow_raw`), apply colour functions to the unpremultiplied blur in the colour pass (`_raster_bdr_color_filtered`), and admit text and restyled `<button>` (`native_frame == 0`). Window raster 555 -> 932‰. Trap: `gradient, colour` backgrounds are NOT `bg_layers_raw` (they land in `background_gradient_from/to`), so they were never the blocker.
## 2026-11-20 — raster lane glyphs from the hinted LCD outline

- **Cause:** the software `raster` lane (`fb_text_ttf_aa_clip_range_adv` -> `_ttf_rasterize_glyph`) rastered the unhinted outline at an `i32` size and placed the baseline with `fb_text_ttf_line_baseline_y` (whole-px ascent, rounded half-leading), so its ink rows missed Chrome at 13.3333 / 21.3333 / 10.6667 / 16 px.
- **Fix:** up to 48 px (Skia `SK_MAX_SIZE_FOR_LCDTEXT`, `FONT_LCD_MAX_SIZE_PX`) and without synthetic bold/italic, the glyph is the exact-area gray scan of the `sfnt_lcd_glyph_outline(…, size_milli)` commands (not the FIR-blurred LCD gray: a 16 px stem never reaches full coverage, which broke an exact-fg-pixel spec); `font_size_milli` rides the glyph cache key; the run baseline is `ly + inline_line_strut_baseline_offset(st)` like the Draw IR lanes.
- **Trap:** do NOT exact-area scan the hinted outline. At 100 px stem-only cap tops (H/I/L) are snapped 0.25 px above the E/F/T bars, and an exact scan inks that sliver as a whole extra row; Chrome's gray text and the 4-row LCD sampler do not. Above 48 px the plain outline stays.
- **Open:** explicit large `line-height` puts raster text lower than Chrome (36 px/50 px: 15..40 vs 11..36), pre-existing.
- **Evidence:** `fractional_font_y_raster_chrome159_spec` AC-3 red on base, green on head; `web_pixel_font_capital_align_no_overlap_spec` 5/5.

## 2026-11-20 — a mid-line run's lead space moves the pen once

- **Bug:** a `#text` run starting mid-line with a collapsible space (` tail `, ` c `) had the space charged twice — the inline loop added it to `inline_x` before the run (layout_engine, `lead_charged` block), and `_lay_inline_text_advance_width_inner` counted it again as an edge space in the box width. Every item after it on the line sat ~4-5 px late (Chrome 159 `A <b>B</b> c <b>D</b>`: `D` at 44, here 49).
- **Fix:** such a one-line run's box is `inline_text_width_after_lead` (exact trimmed width + trailing space, rounded once). `inline_item_width_err_milli` also keeps the exact pen error for a run whose box holds one or two edge spaces (`Lead ` = 35.59 + 4.45 -> 40), so the next run keeps its sub-pixel origin.
- **Spec:** `test/01_unit/browser_engine/inline_tail_pen_chrome159_spec.spl` (base 12 probes off, head 0).
- **Not fixed:** kerning across a trimmed edge space (`A ` is 14.234 in Chrome, kerned A/space; here 15.117 from trimmed `A` + space), so a line of one-letter runs drifts ~1 px.

## 2026-11-20 — text control columns are max(round(a), a) wide

- **Bug:** `form_control_content_w_for_face` always used the ROUNDED OS/2 average width `a` for Liberation Sans `<input>` columns and the EXACT `a` for DejaVu Sans Mono `<textarea>` columns. Chrome 159 uses `c = max(round(a), a)` for both, in device px: 16 px `<input>` (a = 9.273) was 209 here vs Chrome 215, 16 px `<textarea>` (a = 9.633 -> 10) 214 vs 221. Fitted on 12 / 13.3333 / 16 / 20 px, sizes 1..21 and cols 1..40, at k = 1 and 4 — every point exact.
- **Rule:** `<input size=N>` content = `ceil((N - 1) c + round(maxCharWidth))`; `<textarea cols=N>` content = `ceil(N c) + 15k`. The UA 13.3333 px rows (`8N + 17`, `ceil(8.0273 N) + 15`) are unchanged.
- **Spec:** `test/01_unit/browser_engine/form_control_width_dpr_chrome159_spec.spl` (AC-2/3/4/5 red on base, green on head).
- **Trap:** the ratio is not linear in the font size, so fitting one size's widths (as the 2026-11-17 entry did) cannot predict another; measure two sizes whose `a` rounds in opposite directions.
## 2026-11-20 — blurred `text-shadow` on the Draw IR lane

- **Change:** a blurred layer is a text copy with `text-shadow-blur-px`; the executor (`_engine2d_draw_ir_blurred_text_shadow`) draws the run white on black in a CPU offscreen, averages the LCD subpixels into coverage, blurs with sigma = blur/2 (`engine2d_blur_coverage`: Skia triple box for sigma >= 2, else Gaussian), tints, and `draw_image_blend`s it under the text. Both cpu_simd and vulkan take it. The raster routing hold for blurred shadows is gone.
- **Chrome 159 measured:** Chrome's blur extent matches Skia's triple box (blur 8 reaches ~10 px, not a true Gaussian's ~12). Halo rows within 3 per pixel at 1x; dpr4 max channel error 25.
- **Trap:** Engine2D's gray (`set_lcd_text(false)`) glyphs are ~0.4 px high and unhinted vs Chrome's A8 mask; the LCD subpixel mean is the closer mask.
- **Open:** Chrome's mask sits ~0.3 px left for sigma >= 2; the `raster` lane still paints blurred layers sharp.
- **Cost:** a blurred-shadow bare-text page now renders on Draw IR (~4.3 s cold at 1x vs 1.5 s on the raster lane, which drew it wrong); plain pages unchanged (byte-identical, 3.24 s both).

## 2026-11-22 — Skia reference comparison runs (native qualification executable)

- **Gate:** `sh scripts/check/check-skia-web-reference-compare.shs [--scene NAME]... [--out build/test-artifacts/vulkan_2d/<tag>]` with `SKIA_QUAL_BIN` and `SKIA_PROVIDER_SO`. Upstream Skia (Ganesh/Vulkan, pinned `35d5edfa…`) rasterises Simple's web DrawIR on the GB10; the readback SHA-256 must equal the Simple oracle constant read from `src/lib/common/renderdoc/*_oracle.spl`. Measured: web-box 16x16, corpus-case01 and corpus-case06 640x480 all `match`; corpus-case02 FAILs (`edge oracle mismatch`, known bug). Classifier authority: `src/app/ui/skia_reference_compare_receipt.spl`, spec `test/01_unit/app/ui/skia_reference_compare_receipt_spec.spl` (6/6); selftest 9 fixtures.
- **Scope:** Skia leg vs oracle only. The Engine2D physical leg still blocks at device identity (Blocker 9 in `doc/08_tracking/bug/linux_gb10_n2_qualification_executable_blockers_2026-11-18.md`).
- **Native build:** `SIMPLE_NATIVE_BUILD_RUST=1 <seed> native-build ...` compiles the 506-file closure in ~30 s (the interpreted driver took hours). The seed then cannot link Vulkan/provider externs for a non-bootstrap entry (Blocker 8); the bug doc has the manual link recipe and why the Rust archive must come before the core-C one (argv owner).
- **Traps:** the runner accepts only an output dir that is a direct child of `build/test-artifacts/vulkan_2d/` with `[A-Za-z0-9_-]` (else `worker-output-or-provider-domain-invalid`); in a `$(...)` under `set -e`, `cmd; echo $?` never reaches the echo — use `rc=0; cmd || rc=$?`; `vkCreateDevice` on the GB10 is intermittent, so workers are retried (default 3).
- **Lost-half:** merge `e5b290e42a0` also dropped `gpu_provider_device_identity` from `nogc_sync_mut/gpu/provider.spl`; restored, pinned by `provider_spec` (6/6).

## 2026-11-22 — Line-placed form controls hang from the device-px baseline (Chrome 159)

- **Finding first:** the "default controls are 2-3 device rows off at k=4" gap was never a HEIGHT gap. Default heights were already Chrome's (k=4: input / button 85, select 75, textarea 150, checkbox 52). The TOPS were off: every atomic box on a line stayed at k x its CSS top.
- **Chrome (device px, each control alone on a 16px/1.5 Liberation Sans line, k = 1 / 2 / 3 / 4):**
  - line baseline (probed with an empty inline-block): 17 / 35 / 51 / 70. Not k x 17 (34, 51, 68).
  - control baseline from its border-box top: input and button 15 / 30 / 44 / 60; select 14 / 28 / 41 / 55; checkbox, radio, textarea their bottom border edge.
  - so the tops are: input, button 2 / 5 / 7 / 10; select 3 / 7 / 10 / 15; checkbox, radio 4 / 9 / 12 / 18; textarea 0.
- **Rule:** device top = line device baseline - control device baseline. The control baseline is k x (border + padding) plus the control's own DEVICE strut (13.333px `normal`: 12, 24, 35, 48 — 35 at k=3, not 36, the subpixel borrow). A `<select>` has the upper half, rounded up, of its round(1.5k) inner block padding above the label: 1, 2, 3, 3. An auto-height `<button>` is measured from its bottom (its CSS box is 22 px at k=2, 43 device px).
- **Fix:**
  - `form_control_device_baseline_delta` (`..._layout_foundation.spl`): device baseline minus k x CSS baseline. `align_inline_line_device_dy` uses it for the control's ascent / descent and records `line_delta - baseline_delta` per control with `box_device_inline_dy_record`.
  - The entry lives in the device-top table as `DEVICE_TOP_REL + dy`: whole device px RELATIVE to the nearest cursor-placed ancestor. `_html_draw_ir_device_top` (`..._paint_layout.spl`) adds every relative entry on the way up, so the frame and everything it owns move together. `box_device_top_shift` skips relative entries.
  - A `<select>`'s label text gets its own relative entry (`form_control_label_device_dy`, recorded in the form-control branch of `..._layout_engine.spl`): the label sits on the line baseline, the frame one row lower at k=4.
- **Trap — do not read a baseline off glyph rows.** The top row of an `O` differs by one between the two rasterisers; the empty inline-block probe gives the baseline as a number.
- **Trap — k=3 is the scale that tells the rules apart.** At k = 2 and 4 the control's device strut equals k x CSS, so "add the line delta" passes; at k=3 the line delta is 0 and the whole move comes from the control's own strut (44 for 45).
- **Not done (named, not hidden):**
  - `<input type=submit value>` paints no label at all, at any scale (frame only).
  - The value text of a text `<input>` is owned by the input and moves with the frame: one device row low at k=3 only (baseline delta -1), exact at k = 2 and 4.
  - An `<img>` or inline-block on a text line still keeps k x its CSS top; the same rule applies (`bottom_edge_baseline` branch of `align_inline_line_device_dy`) but was left out of this lane.
- **Spec:** `test/01_unit/browser_engine/form_control_height_dpr_chrome159_spec.spl` (4 cases; base 6b508da8f57 1/4 — the 1x guard — head 4/4).
- **Catalog 4x:** forms-media 3.06 -> 3.04 (the checkbox and radio rows 664 -> 666, 793 -> 795 as in Chrome; the styled `padding:8px` controls already matched and did not move).
## 2026-11-22 — media-controls vector parts (animation page lane)

- **Page fact:** the catalog `animation` page has no CSS animation, transition or transform; it is the canvas / svg / audio / video probe tab. Chrome's capture is a plain load-event screenshot and the Simple side a static render, so there is no capture-time mismatch to look for.
- **Change:** `media_control_chrome.spl` (new) rasterizes Chrome's media-controls icons as device-px spans — Material `play_arrow`, `volume_up`, `more_vert` at 20/24 and the 4 px timeline stadium — and `_html_draw_ir_replaced_media_commands` lowers them like the checkbox parts. Audio 300x54: 1,015 -> 467 px off at 1x, 11,629 -> 3,578 at 4x; video 120x150: 388 -> 0, 6,059 -> 25.
- **Chrome 159 measured:** audio icon boxes are 20x20 at x 16 / w-68 / w-36, centred on h/2; play and volume are black at 30 % (disabled without a source), the kebab solid black, the track black at 20 % from x 129.27 (129.08 at 1x) to w-90. Video: track x 16..w-16, y h-24..h-20, kebab centred on (w-24, h-48), both white at 30 %.
- **Open:** the audio `0:00 / 0:00` time text (14 px LCD text at x 48..114) is the rest of the audio residual, and the track's left end follows its advance. A wide video's play / time / volume / fullscreen buttons are not modelled, and a short video's scrim is wrong (Chrome's gradient is not a % of the height).
- **Trap:** a probe page with no text tag takes the 1x `simple_web_layout_render_html_pixels` route, which paints no media controls at all — add a `<p>` or call the device-scale entry point. `position:absolute` audio/video paint nothing.
- **Trap:** Skia's 1x kebab dots are a hair narrower than a circle (side pixels 0x78 vs 0x6f on #f1f3f4): 12 px stay 9 off, one over the catalog tolerance.
- **Handover:** inline replaced boxes after a collapsed space sit one CSS px left (space advance 4 vs 4.45; whole-CSS-px boxes at device scale 4) — red spec `inline_replaced_fractional_x_chrome159_spec.spl`, for the layout lane.
- **Spec:** `test/01_unit/browser_engine/media_controls_paint_chrome159_spec.spl` (0/7 on base, 7/7 on head).


## 2026-11-22 — round horizontal stems keep their natural width (Chrome 159 light autohinter)

- **Measured (pixel attribution, html / forms-media / overview / evidence / tab-bar at 1x):** 95..99% of every page's mismatch sits under a text rect; no layout offset. Inside the text, the heavy deltas were the top and bottom arcs of round lowercase letters (`a e o s c p`): Chrome's arc is about 1.2 px thick below the x-height row, ours was about 1.0 px.
- **Root cause:** `_lcd_hint_knots` warps y through the blue-zone knots, and the overshoot collapses onto the reference below half a pixel. FreeType moves EDGES instead: a curve extremum is a round edge, the outer and inner extremum of an arc are a stem, the outer edge takes the zone fit and the inner edge follows at the natural width. The y warp took the collapsed overshoot (0.16..0.19 px at 16 px) out of the stroke.
- **Change (`sfnt_glyf.spl`):**
  - `_hstem_round_extrema` adds round edges to the stem pairing: an on-curve point with an off-curve neighbour whose two neighbours lie on its near-horizontal tangent (1:14) and continue in the same x direction.
  - `_hstem_knots` builds a glyph's knots from its OWN blue edges and blue extrema (`_hstem_edge_knot`), not from every zone. An `o` has no edge on the flat baseline reference; a knot there squashed the arc between the collapsed overshoot and the inner edge.
- **Spec:** `glyph_round_stem_chrome159_spec` (0/3 on base, 3/3 after).
- **Fixture (Liberation Sans 16 / 13.333 / 18.72 bold / 24 bold, mono 12, 400x100):** 4329 -> 3709 (round stems) -> 3631 (own-edge knots) mismatching px.
- **Catalog 1x:**

  | page | before | after |
  |---|---|---|
  | html | 1.77 | 1.49 |
  | forms-media | 2.15 | 1.78 |
  | overview | 1.10 | 0.89 |
  | evidence | 0.67 | 0.52 |
  | tab-bar | 0.31 | 0.30 |

- **Trap — a mid-quad extremum is not a round edge here.** Only an on-curve extremum point is detected. A curve whose extreme is a control point keeps the blue-extremum knot only (FreeType fits the control point).
- **Trap — the o bottom centre stays off.** Chrome `e7dfc7`, ours `eff7e7` (was `ffffff`): Chrome's bottom arc is heavier on its right half. The stem fit is symmetric, so pin the shoulder pixel (7,17), not the centre.
- **Open, measured, not fixed (page lanes html / forms-media):**
  - **Device scale 4, text pens:** `draw_ir_composition_at_device_scale` multiplies the whole-CSS-px `advance_widths` by k, so a glyph pen is a multiple of 4 device px. Chrome keeps the fractional advance (E 10.672 px -> 42.69 device px): per-glyph offsets of -2..+2 device px on `Examples show`. The grayscale raster also drops the bearing fraction (`_outline_edges(..., bounds.left * scale, ...)`): Chrome's E stem is 21.26..27.22, ours 21..27. Needs a fractional device advance on the Draw IR text command (producer, device-scale pass, Engine2D consumer).
  - **18.72 px bold (h3):** some glyphs (`a`, `p`) sit about 0.2..0.3 px right of Chrome's while `m` matches: a per-glyph LCD phase difference at fractional sizes.
  - **Tool note:** element attribution needs the rect dump in standards mode. Prepending anything before `<!doctype>` puts Chrome in quirks mode and moves every rect about 14 px.

## 2026-11-22 — fractional sizes at Chrome's font-cache-key size; quarter-phase ties (page lane html / forms-media)

- **Measured (Chrome 159, Range rects of `m` runs):** the size Chrome shapes and rasterises `font-size: S` at is `trunc(trunc_f32(S * 100) / 100 * 64) / 64`. Blink keys its font cache on `(unsigned)(size * 100)` in float32 and creates the platform font at that size; Skia then truncates to 26.6. 18.72 (UA h3) is float 18.7199993 -> x100 1871.9999 -> 18.71 -> **1197/64**, not 1198/64. 37.44 -> 2395, 17.72 -> 1133, 19.72 -> 1261, but 20.72 x100 rounds to 2072.0 in float32 and keeps 1326; 13.3333 -> 853, 13.28 (h5) -> 849, 10.72 (h6) -> 686.
- **Root cause of the open "18.72 bold per-glyph LCD phase" item above:** `_fr_size_26_6` scaled every fractional pen by 1198/64, 0.09% long. That crossed a quarter phase on about half of each h3 run's glyphs (ink +0.25..0.31 px right). The bold face was not the cause; 18.72 regular showed the same.
- **Change (`font_renderer.spl`):** `_fr_size_26_6` emulates the float32 key truncation. Spec: `font_cache_key_size_chrome159_spec` (1/4 -> 4/4, then AC-5 4/5 -> 5/5). The LCD outline is rasterised at the keyed size too (`x_milli` = keyed 26.6 size in milli): AC-5 edge pixels go from 16 to 8 levels off, which is exactly at the 8-level tolerance. AC-2 (37.44) allows 2/64 px: Chrome's 39902/64 width is 1.85/64 above the linear 2395/64 model, a residual still unexplained. The old 2396/64 width was 15/64 off.
- **Quarter-phase ties:** at an integer size a pen is a whole number of font units (16 px Liberation: 1/128 px), so pens at k/8 px are exact ties, and Chrome (SkFixed + 1/8, floor to 1/4) rounds them up. The engine summed per-glyph advances that were each rounded to milli-px, so a tie could come out 3 milli short and round down (`p` at 190.622). Fix: `_lcd_apply_pen_phases` snaps integer-size pens to the unit grid (`_fr_units_per_em`). The snap never grows the error. `whole` (the layout pens) is unchanged. Spec: `lcd_quarter_phase_tie_chrome159_spec` (0/1 -> 1/1).
- **Handed off (layout lane), not fixed here:** a run inside an inline element after a collapsible space (`Keyboard samples: <kbd>`, `<kbd>A</kbd> <kbd>B</kbd>`) gets `pen-origin-milli` 0, because the trimmed trailing space breaks `inline_pen_err`. Its glyphs land 0.41 / 0.77 px left. This is 2,050 of the html page's 9,599 mismatching px at 1x. A text run that follows an element keeps its origin. Spec: `inline_element_pen_origin_chrome159_spec` (`@tag:in-development`, 0/2).
- **Trap — monospace here is DejaVu Sans Mono** (1233 units = 9.6328 px at 16 px), not Liberation Mono.
- **Trap — `cols`-style ink-run attribution merges touching glyphs.** Compare per-glyph centroids on a `letter-spacing` fixture instead. A pen error shows as a ±0.25 step, a raster error as an ink-sum change with the centroid unmoved.
- **Remaining 1x text residual (this lane, open):** per-glyph raster shape at 16 px. Word positions match within 0.06 px, while ink runs 0.3..0.5% lighter. The worst glyphs are `a` (top and bottom arc rows), `s`, `o`, `q`, `g` and digits `3 5 6 8 9`, at 20..40 mismatching px per glyph; `i l j t` sit at 0..3.
- **Perf (html 1x, 3 alternations, idle box, same seed binary):** base 40.15 s, round stems 40.50 s (+0.9%), font-cache-key size 40.68 s (+0.45%), final 40.67 s. The tie snap adds nothing measurable. Max RSS is about 800 MB on every commit.

## 2026-11-22 — css-layout page breakdown (lane 4b): no box-layout cause, three text/line causes handed over

- **Result:** on the catalog css-layout page (1x 2.13, 4x 3.18) every box rect matches Chrome; nothing is wrong in `layout_box` / `layout_float` / `layout_table` / `layout_core` / `layout_insets`. No source change in this lane.
- **4x ranking (348,217 px):** section box-shadow missing at dpr4 147.7k (42%); glyph raster residual ~137.5k (39%); `div.scroll` scrollbar + dashes 28.3k (8%); word pen on whole CSS px ~26.3k (7.5%); wrapped line after a `code` line ~6.3k (1.8%); `.badge` ~2k. **1x (14,579 px):** glyph raster 85%, `div.scroll` 11%, section edges 2.5%.
- **New red specs (owner: layout_engine / layout_foundation / layout_text lane):**
  - `dpr4_word_pen_fraction_chrome159_spec` (0/3): at device scale 4 each word starts on a whole CSS px; Chrome keeps the fraction (`b` at 23.344 CSS px = column 98, engine 96).
  - `dpr4_wrapped_line_device_height_chrome159_spec` (1/3): a wrapped block is 96 + 96 device px where Chrome has 97 + 96 (16px monospace `code` on line 1); line 2 and the next block sit one device row high. One-line blocks were already right.
  - `hyphen_break_opportunity_chrome159_spec` (1/3): no break after U+002D inside a word; Chrome breaks `keyword-|number`.
- **Method:** attribute mismatched px to the deepest Chrome rect, then split text into position and raster by the best per-word shift (x in -3..3, y in -2..2 device px). At 1x the best shift is (0,0) for 198 of 200 clusters, so 1x text mismatch is raster only.
- **Trap:** Chrome rects dumped at K=1 are not the K=4 geometry (a `code` line is 24.25 CSS px at K=4); dump rects at the scale you compare.

## 2026-11-22 — pd-layout: wrapped-line device height and hyphen break fixed; dpr4 word pen still open

- **Hyphen break (layout_text):** a break opportunity after U+002D inside a word (Chrome 159 line-break class HY). `hyphen_break_opportunity_chrome159_spec` 1/3 -> 3/3.
- **Wrapped-line device height (layout_engine + layout_foundation):** at k>1 a wrapped run that ends its block, with other boxes on its first line, now takes the multi-line path. Lines 2..n move down by the first line's device-height fraction (`text_device_dy_rest_add`), e.g. a 16px monospace `code` line is 97 device px at k=4, not 96. `dpr4_wrapped_line_device_height_chrome159_spec` 1/3 -> 3/3.
- **Word pen: STILL OPEN; the tried fix regressed and was dropped.** `dpr4_word_pen_fraction_chrome159_spec` stays red (0/3). Tried: at k>1 each non-shaped text command also carried `device-advance-widths` (the run's advances at k x the font size), and the device-scale pass swapped them in. Result: spec 3/3, but the 4x catalog rose on 5 pages: html 2.37 -> 3.02, css-layout 3.12 -> 3.48, css-paint 3.44 -> 4.44, forms-media -> 3.56, animation 3.31 -> 4.38. Cause, measured on the css-layout `Examples show selected values; ...` line (16px sans-serif): with the swap, word ink starts drift steadily right of Chrome (+0, +1, +2, +4 ... +14, +18 device px across one line, about 0.65%). With 4 x whole-CSS-px advances they stay within ±2 of Chrome. Yet `resolve_font_metrics_with_language_milli` at 64px sums to the exact 4 x 16px width (2796 vs 2796.1), so where the extra width enters is NOT localized. The probe passed language `en` and size 64000 directly, while paint passes `_html_text_language(..)` and `font_milli_of(..) * k`; the lane line also ends 18 px past Chrome at its last word start but has the same ink extent, which suggests the tail is clipped at the CSS-width clip rect. Short runs (`a b c`, ±1 px) hide it. **Next:** first re-run the probe with the exact language and size the paint call uses; then render that one line at k=4 and log the advances the raster actually steps by against the `device-advance-widths` it was handed. Extend the spec with a long-line case (word starts at the line end) before retrying. The tried commit is kept locally as branch `wip/pd-layout-word-pen-drift-20261122`.
- **Import rule:** new layout_foundation imports in layout_engine go on their OWN `use` line, because other lanes edit the big shared import line.
## 2026-11-22 — an edge space is measured with its run (letter/space kern)

- **Cause:** metrics are measured over the TRIMMED text and the edge space was charged as a flat `resolved_space_milli`. Chrome shapes run+space as one run, so the (letter, space) kern pair applies (`A ` 14.234 not 10.672 + 4.453; Liberation Sans 16: A -0.883, L -0.602, T/Y -0.289, also on the lead side). `resolve_font_metrics_with_language_milli` already kerns the space, so no font change was needed.
- **Fix:** `Style.resolved_lead_space_milli` / `resolved_trail_space_milli` = width(" "+text) / width(text+" ") minus width(text), computed in the style stage (core.spl) ONLY for a run that has that edge space (not nowrap/rtl/letter-spaced). Used by `inline_text_width_after_lead`, `_lay_inline_text_advance_width_inner`, the lead-charge pen error (layout_engine) and `inline_item_width_err_milli` (kerned-edge candidates).
- **Spec:** `test/01_unit/browser_engine/inline_space_kern_chrome159_spec.spl` (ink-run starts from the Chrome screenshot; red on base from the 4th run).
- **Not fixed:** a text run INSIDE an inline element (`<b>F</b>`) gets no pen-origin (`text_pen_origin_record` only fires for a direct `#text` child), so lines with 8+ alternating runs still drift ~1-2 px; the spec stops at 7 runs.
## Button width without label_slack (2026-11-22)
- `label_slack` (a `<button>` label up to 1 px over the content box stays on one line) is deleted: since the LayoutUnit flex widths (`box_frac_w_*`, `form_control_button_frac_delta_milli_px`) the tab row, AC-11 and every form-control spec stay green without it.
- `button_device_extra_w` (layout_foundation): an auto-width `<button>` at k > 1 is sized in device px from its fractional label, as `select_device_extra_w` is for a select. `Go` is 135.14 / 143.14 device px at k = 4 (default / padded) in Chrome 159, was 136 / 144. Recorded via `box_device_extra_w_record` at the end of the generic block layout; skipped for authored width, `flex-grow`, a flex/grid parent and any button followed by a box (that box keeps its CSS-snapped x, so narrowing opened a 1 px gap and raised tab-bar at 4x 0.20 -> 0.23). Pinned by `button_label_width_chrome159_spec`.
- Still open: boxes after a button keep their CSS-snapped x at k > 1.

## 2026-11-22 — a box taller than the frame lost its box-shadow (Engine2D admission)

- **Was:** `_e2d_box_shadow_call_safe` (`engine2d/draw_ir_box_effects.spl`) bounded the WHOLE blur-expanded shadow rect to 16,777,216 px. A catalog panel is 852 x 16939 CSS px: 15.07M px at scale 1 (just under), 231M at device scale 4, so every page lost both section shadows at dpr4 (flat `238` where Chrome falls `237..225`). About 165k px per page, 43% of the 4x mismatch on css-paint / css-layout / animation. Any page past ~18,800 px loses it at scale 1 too.
- **Rule:** the painter (`emu_draw_shadow_rect`, the Vulkan kernel) reads and writes only the part of the shadow inside the frame, and its profiles are O(w + h). With a known frame the bound is that in-frame part (plus a per-axis sample cap). A caller with no frame (0, 0) keeps the old whole-rect bound.
- **Change:** `frame_w` / `frame_h` (default 0) on `engine2d_draw_ir_typed_shadow_geometry_safe`, `..._legacy_shadow_safe`, `..._render_typed_outer_shadows`, `..._render_legacy_shadow`, `..._has_outer_shadow`; `draw_ir_adv` passes `fb_w` / `fb_h` (render box) and `width` / `height` (fresh-device admission).
- **Pin:** `box_shadow_tall_box_chrome159_spec` (60 x 400000 box, Chrome row 150: `F8 F3 EB E1 D4 C5 B5 A2` left, mirrored right). Base: raster ok, cpu_simd and vulkan 16/16 off. Head 3/3.
- **Trap — a 1x-clean element can be absent at 4x.** The per-element attribution (below) showed `body>main` owning 97,724 mismatched px at 4x and 53 at 1x; that jump, identical on three pages, was the admission cap, not a blur-kernel difference.
- **Method — per-element attribution.** Append a `<script>` that dumps `getBoundingClientRect` of every element and `Range.getClientRects` of every text node into a hidden `<pre>`, read it with `--dump-dom --hide-scrollbars --window-size=900,960`, then give each mismatched pixel (tolerance 8) to the deepest rect over it, text rects first. A best-shift search (+-3 px) per rect separates a position offset from a raster difference.
- **css-paint residual at 1x after this (16,273 px):** ~92% text raster at an exact pen (2.2..2.6 px per px of run width), 8.4% table-cell text at a fractional column edge (`Expected` / `Visible` / `Aligned`, pen 425.36, 7.5..8.5 px per px), 7.3% the 18.72 px bold h3 (pens drift ~1.5 px right by the end of a 271 px line), <1% box edges.
- **Handed to the layout lane (not landed here):** table cell text pen origin. Chrome sizes auto columns in 1/64 px: column i is `floor(width * max_i / sum(max))`, the last takes the rest (measured on 2- and 3-column tables). Red spec `table_cell_pen_origin_chrome159_spec` (1/3 on base).

## 2026-11-23 — the admitted tall box-shadow cost 4x render time 4-5x (perf, byte-identical fix)

- **Was:** after the tall-box admission fix, device-scale 4 pages took 500-560 s (base ~110 s). One `section` (3408 x 67908 device px) cost 280 s and a second 198 s, all in `emu_draw_shadow_rect`, measured with temporary timing:
  `draw` 239 s, `rows` 15.5 s, `read` 3.4 s, `prof` 0.8 s for one 3600 x 3040 region.
- **Trap 1 — `self.buf.write_span` on a FIELD copies the whole surface per call** in the interpreter: 1.4 ms per row at 3600 x 3040, against ~1 us for a local array. Another trap: `SoftwareBackend.draw_image` under an active clip went per pixel (`sw_set_pixel`, ~22 us/px). Fix: each row is one clipped span written into a local `buf`, stored back once; only a mask still goes per pixel.
- **Trap 2 — profiles over the whole box:** `engine2d_blur_step_profile(start, end, lo, hi, ...)` samples only `[lo, hi)` and its result does not depend on that window, so sample the in-frame span only.
- **Change:** `emu_draw_shadow_rect_outside` (hole rect left untouched; `emu_draw_shadow_rect` = no hole). It composites each band with a native row compare and a copy of the previous composed row. `Engine2D.draw_shadow_rect_outside` falls back to the whole shadow on device lanes (Vulkan/CUDA). The Draw IR box passes the border-box rows outside the corner bands (`engine2d_draw_ir_box_straight_rows`) only when the knockout restores them or an opaque plain colour fill covers them.
- **Measured (cpu_simd, interpreter, 7b87b490ae5 -> this):** 4x html 498->114 s, css-layout 540->130, css-paint 557->112, forms-media 517->108, animation 543->108 (base css-paint 114); 1x 40-49 s -> 13-20 s. All ten .ppm frames are byte-identical.
## General dev2 Devanagari shaping (2026-11-22)

- **Was:** only the literal word हिन्दी was admitted to the shaped lane (`_selected_text` in `ot_layout_shaper.spl`, a hard-coded reorder in `_nominal`). Any other Devanagari run had `glyph_run.valid == false` and took the unshaped per-codepoint fallback (`नमस्ते दुनिया` 103 px, Chrome 72.9).
- **Now:** `src/lib/skia/feature/shaper/indic_dev2.spl` shapes any dev2 run the HarfBuzz way; `_resolve_dev2_run` (`ot_layout_shaper.spl`) runs GPOS on its output. Segmentation and both reorderings live in `indic_syllable.spl` (font-free, next section); `indic_dev2.spl` is its only consumer and holds the face probes and the GSUB stages.
  - Stage order, each stage per syllable in lookup-index order: initial reorder -> `locl ccmp` -> `nukt` `akhn` `rphf` `rkrf` `blwf` `abvf` `half` `pstf` `vatu` `cjct` (one stage each) -> final reorder -> `pres abvs blws psts haln rlig calt clig liga rclt`.
  - Masks: `rphf` on the reph Ra+halant, `half`+`blwf` before the base, `blwf`+`abvf`+`pstf` after it; a ZWNJ clears `half` on what precedes it. Masks are restored from the first component after every stage (the GSUB ligature code ANDs component masks; HarfBuzz keeps the first glyph's).
  - Base selection and reph need the face: a consonant is below-base when `blwf` ligates it with the halant (either order), and the leading Ra+halant is a reph only when `rphf` ligates it. Both are probed by running that feature on a two-glyph record list.
  - Known difference: HarfBuzz runs `locl ccmp` before the initial reorder. Not visible in the 42 measured words.
  - `indic_final_order` gets category 0 for a ligated glyph whose first component is a halant, nukta, joiner or matra (rakar = halant + ra via `blwf` is not an explicit halant).
  - Clusters are HarfBuzz level 0 (Chrome's): grapheme start (marks, halant, nukta, ZWJ continue; ZWNJ does not), a ligature takes its smallest component, the final reorder merges pre-base matra..base and syllable start..reph, then a monotone merge. हिन्दी -> 0 0 2 4 4 (`selected_devanagari_spec` Serif witness); `नमस्ते दुनिया` still spaces as Chrome.
  - Final reorder: pre-base matra goes after the last explicit halant before the base (else stays first); reph goes after the first explicit halant before the base, else to the syllable end before anusvara/visarga.
  - ZWJ/ZWNJ that no lookup consumed become the space glyph with zero advance (Chrome shows glyph 3). `र्‍य` consumes the ZWJ in the eyelash ligature.
  - U+0958..095F are split into base + nukta (two items on one source index); न/र/ळ + nukta compose to U+0929/0931/0934 when the face maps them.
- **Fail closed (returns None, fallback as before):** a mark with no base (`indic_syllable` kind 4; Chrome inserts a dotted circle), an unmapped codepoint, a face with `pref` or `init` lookups, or any GSUB stage the validator rejects.
- **GPOS gate removed:** `_gpos_mask` let abvm/blwm start only on codepoints U+093E..094D, which excluded reph, nukta and anusvara glyphs. dev2 now runs every GPOS feature on every glyph, like Arabic. `mark`/`mkmk` are still not in the dev2 GPOS tag list (HarfBuzz applies them).
- **Font facts (NotoSansDevanagari, dev2 dflt; there is no HIN LangSys):** ccmp 217,219; nukt 101; akhn 102,103; rphf 104; rkrf 105,106; blwf 113; half 114-117; cjct 121; pres 40,68,121,41,39,46,85. No locl/pref/pstf/vatu/init/haln. Glyph 506 reph, 508 rakar, 103 halant, 3 space. ई is two glyphs (7 + 506) after ccmp.
- **Measuring Chrome's glyph ids:** `--print-to-pdf`; Skia's PDF Type3 fonts keep the face's glyph ids (`/CharProcs /g<hex gid>`, `/Differences` maps the one-byte codes). Keep a page to 30 words; a second PDF page makes the list harder to read. Text-op x is the pen position including the GPOS x offset.
- **Trap:** the page command width is whole px, floored (72 for Chrome's 72.90625).
- **Cost (seed interpreter):** हिन्दी 8.5 s on base, 8.9 s now; a newly admitted 11-glyph run costs 13.8 s. Each stage call re-validates its lookups.
- **Spec:** `test/01_unit/browser_engine/devanagari_dev2_shaping_chrome159_spec.spl` 8 examples (19 words). Base: 7 of 8 failing.
- **Open:** broken clusters (dotted circle insertion); `init`/`pref`; explicit `font-feature-settings` are ignored for dev2; other Indic scripts.

- **Change:** a blurred layer is a text copy with `text-shadow-blur-px`; the executor (`_engine2d_draw_ir_blurred_text_shadow`) draws the run white on black in a CPU offscreen, averages the LCD subpixels into coverage, blurs with sigma = blur/2 (`engine2d_blur_coverage`: Skia triple box for sigma >= 2, else Gaussian), tints, and `draw_image_blend`s it under the text. Both cpu_simd and vulkan take it. The raster routing hold for blurred shadows is gone.
- **Chrome 159 measured:** Chrome's blur extent matches Skia's triple box (blur 8 reaches ~10 px, not a true Gaussian's ~12). Halo rows within 3 per pixel at 1x; dpr4 max channel error 25.
- **Trap:** Engine2D's gray (`set_lcd_text(false)`) glyphs are ~0.4 px high and unhinted vs Chrome's A8 mask; the LCD subpixel mean is the closer mask.
- **Open:** Chrome's mask sits ~0.3 px left for sigma >= 2; the `raster` lane still paints blurred layers sharp.
- **Cost:** a blurred-shadow bare-text page now renders on Draw IR (~4.3 s cold at 1x vs 1.5 s on the raster lane, which drew it wrong); plain pages unchanged (byte-identical, 3.24 s both).

## 2026-11-22 — Indic (Devanagari dev2) syllables and reordering, font-free

- **Module:** `src/lib/skia/feature/shaper/indic_syllable.spl` — pure codepoints -> `IndicClusters` (no font, no I/O). `indic_clusters` (Devanagari defaults: Ra is the only below-base consonant, `rphf` present), `indic_clusters_with_forms` (face-probed below-base / post-base codepoint sets), `indic_final_order` (post-GSUB permutation for one syllable). Not yet wired into `shaper.spl`; the dev2 GSUB lane consumes it.
- **Model:** HarfBuzz's Indic shaper, same category/position numbers (position 1 reph, 2 pre-base matra, 3 pre-base consonant, 4 base, 8 below, 9 matra, 11 post, 13 modifier). Syllables come from a longest-match over consonant / vowel / standalone / symbol / broken, ties to the earlier kind.
- **Rules worth remembering:** base = last consonant with no below-base form (so `त्र` has base `त`, `प्र` base `प`); reph = Ra + halant at syllable start, at least 3 items, third not a joiner, and another consonant exists; a pre-base matra sorts AFTER the reph and BEFORE the pre-base consonants; HarfBuzz ORs `half|blwf` onto every item before the base, reph and matra included; a ZWNJ strips `half` back to its consonant; `क् ZWNJ` ends the syllable, `क् ZWJ ष` does not.
- **Final reorder:** the matra only moves when an explicit halant survives GSUB before the base (it goes after it and a following joiner); reph goes to the end of the syllable, before position-13 items and before a final halant that follows a matra.
- **Trap:** `Ra + halant + matra` is a BROKEN cluster (longer than the 2-item consonant syllable): a dotted circle is inserted in front, becomes the base, and Ra goes below-base — no reph.
- **Open:** Vedic Extensions (1CD0-1CFF) and A8F2-A8FF are category 0 here; only Devanagari is covered (other Indic scripts need their own base/reph configuration).
- **Spec:** `test/01_unit/lib/skia/indic_syllable_spec.spl` (55 examples; red on base as a missing module).

## 2026-11-23 — dev2 lane A: HarfBuzz clusters, ROUND composite glyphs in shaped runs

- **Clusters:** `indic_dev2_substitute` returns HarfBuzz level-0 clusters (was: every glyph of a syllable at the syllable start, which regressed the Serif `हिन्दी` witness 0 0 2 4 4 in `selected_devanagari_spec`).
- **Shaped run falls back to the raster lane** (symptom: ink x0=21, a matra missing) whenever the run holds (a) a composite flagged ROUND_XY_TO_GRID (4), which `_parse_glyph` (sfnt_glyf.spl) rejected — Noto's ो ौ क़ ज़ (42 43 221 224, flags 550/7). FIXED: the round flag is ignored (FreeType ignores it unless bytecode-hinted). (b) An EMPTY glyph — the space glyph 3 a hidden ZWJ/ZWNJ becomes, or 785, the empty placeholder after the anusvara i-matra 559/564 — because `_stage_selected_glyph_run_active` (font_renderer.spl) rejects any glyph with width 0. NOT fixed: skipping empty glyphs there was tried and backed out — it also stops every Arabic run with a space from falling back, and the shaped path (i) never moves glyph xs for letter-/word-spacing and (ii) ends RTL ink one column short (95 vs Chrome 96): `shaped_run_spacing_chrome159_spec` 6/6 -> 3/6. Precondition to land the skip: spacing applied to shaped glyph xs (paint_draw_ir has the per-codepoint gap and the clusters; RTL gap trails each unit on its visual left) and the RTL 1px ink. Waiting on it: corpus AC-8 (joiners) and सिंह / हिंदी (785).
- **Corpus** (`devanagari_corpus_chrome159_spec`, in-development): glyph ids and widths match Chrome for all 35 words; what stays red is the empty-glyph fallback above, not GSUB. Count is in the lane report (base moved under it).
- **Trap:** the draw-IR glyph ids (`_gids`) can be right while the pixels come from the raster lane — the bare-text pixel route silently keeps the raster frame when a Draw IR text command fails to stage. Compare ink, not just ids.
- **Trap:** `simple run` of a shaping probe grows ~2 GB per word (killed at 6 G after 3 words); probe 2 words per process.
## 2026-11-22 — Control follow-ups at device scale: push-button inputs, atomic inlines, input value glyphs

- **`<input type=submit|button|reset>` "paints no label" was a WIDTH bug.** The label was painted, but centred in a 185 px box: every such input took the 20-column text-field width (`form_control_intrinsic_content_w`) and the text field's 2 px inline padding. Chrome 159 sizes it like a `<button>`: label + `padding: 1px 6px` + 2 px border. getBoundingClientRect at 13.333px Liberation Sans: `value="Go"` 33.78, `type=submit` 57.48 (`Submit`), `type=reset` 50.83 (`Reset`), `type=button` with no value 16. Painted widths at K=1 are the fraction ROUNDED (34 / 57 / 51 / 16), not ceiled as a `<select>` label is.
  - Fix: `input_auto_content_w` (`layout_text.spl`) is used at all three input width sites (`text_control_auto_outer_w`, the intrinsic-width pass and placement in `layout_engine.spl`); `form_control_ua_box_decls` (`core.spl`) adds `padding:1px 6px` for push-button inputs.
  - **Trap:** measure the label with `resolve_font_metrics_with_language_milli(…, 13333)`. Its `width_milli` reads `Submit` 41.481 (Chrome 41.484). The oversampled whole-px measure used for `<select>` reads 41.500 at x10 and x12, which rounds the wrong way (58 for 57).
  - Device widths at K>1 stay K x CSS (Chrome 135 / 230 / 203 device px at K=4 where K x CSS is 136 / 228 / 204). The button lane's `button_device_extra_w` is the model if this is needed.
- **Empty inline-block / `<img>` on a line at K>1:** same rule as #10790's controls. The `bottom_edge_baseline` branch of `align_inline_line_device_dy` now records the box as a line-placed atomic with delta `extra_h`, so it hangs from the device baseline (K=4: 30-69 for 28-67; K=2 one row; K=3 unchanged since 51 = 3 x 17).
- **HELD (branch `work/webrender-input-value-glyph-held-20261122`, needs owner approval): an input's painted value is 13 px, not 13.333.** The Draw IR value command (`_html_draw_ir_input_value_command`) resolves real advances at the float size but carries no `font-size-milli`, so the glyphs rasterise at 13 px: `Go` inks columns 5-18 for Chrome's 5-20 and is one row short at K=4. With the prop added, the value is one device row LOW at K=3. It also needs the strut's device offset that a `<button>` label's `#text` run gets: device strut baseline - K x CSS strut baseline + `text_device_painter_dy`, carried as `device-y-offset`. With both, `Go` in a text field or push button inks Chrome's rows at K = 1..4.
  - **Why held:** `form_control_paint_chrome159_spec` AC-11 pins the styled `Simple` field's FIRST ink row at K=4 as 45. Base hits it only because the 13 px glyph is shorter. Measured ink rows / columns (inside the field, K=1..4):

    | | K=1 | K=2 | K=3 | K=4 |
    |--|--|--|--|--|
    | Chrome | 9-9 11-20 c7-45 | 17-40 c14-91 | 24-60 c21-137 | 33-82 c27-183 |
    | base | 9-20 c7-44 | 17-40 c14-90 | 25-60 c21-136 | 33-81 c26-181 |
    | held fix | 9-9 11-20 c7-45 | 17-40 c14-90 | 23-60 c20-136 | 34-82 c26-182 |

    Bottoms and columns improve, but the TOP row of `S` / `l` is off by one either way. `<button>Submit</button>`, whose text path is unchanged, shows the same top-row miss (K=3 21 for Chrome 22, K=4 32 for 31). The miss is the glyph-top raster, not the input. Repinning AC-11 to the descender row (82) is an owner call.
  - The K=3 "one row low" reported for the text field in #10790 came from that wrong glyph size: 13 px glyphs matched `Hg` at K=3 and missed at K=4.
- **Found, not fixed (1x layout, owner: inline baselines in `layout_engine`):** an `inline-block` whose only child is a BLOCK (`<span style="display:inline-block"><div style="height:10px"></div></span>`) has no line box, so its baseline is its bottom margin edge. Chrome 159 puts it on the text baseline (K=1 rows 100-109 on a line at 93). This engine places it at the line top (93-102), 7 CSS px high, because `bottom_edge_baseline` requires `child_count == 0`.
- **Specs:** `input_button_label_chrome159_spec` (base 0/3, head 3/3; the held branch adds the K=3/4 rows and the K=1 columns), `inline_atomic_device_baseline_chrome159_spec` (base 2/4, head 4/4). Held: `input_value_device_rows_chrome159_spec` (base 2/5, fix 5/5).
## 2026-11-22 — Inline pen error carried across runs, atomic boxes and replaced boxes (Chrome 159)

- **Mechanism:** the inline loop (`layout_with_style_flow`, `..._layout_engine.spl`) keeps the cursor's exact-minus-integer error `inline_err_milli` (valid only while the cursor stays at `inline_err_x` / `inline_err_y`, see `inline_pen_err`). After each item whose width error is known (`inline_item_width_err_milli`), whole pixels of the error move the cursor (`inline_pen_err_carry_px`, to nearest), so the error left stays within half a pixel. The carry runs only after an ITEM, never at a run's lead space (that broke a wrapped run's first-line inset).
- **Run inside an inline element:** `<b>F</b>` got no pen origin (`text_pen_origin_record` fired only for a direct `#text` child), so 8+ alternating runs drifted 1-2 px. The element's one run now records the element's pen origin. Spec `inline_element_run_pen_chrome159_spec.spl` (the 9th run at 110, not 107).
- **Box after an auto-width `<button>`:** the box holds the label rounded UP, Chrome keeps the fraction (`Go` 33.785 px in 34, `Submit` 41.484 in 42): `inline_button_width_err_milli`. A device-sized control (default `<input>` 719 device px at k = 4 in a 185 CSS px box) contributes `box_device_extra_w / k`. At k > 1 an atomic inline box records `box_device_dx` (k x its pen error, nearest device px); `_html_draw_ir_device_dx` (`..._paint_layout.spl`) adds it to the box's subtree commands as the draw-IR prop `device-x-offset`, which `draw_ir_device_scale.spl` applies after scaling and strips (never a CSS length). Spec `button_following_box_x_chrome159_spec.spl` (4 rows incl. input/select/textarea at k = 4).
- **Replaced box sized by a whole-px `width` attribute** (canvas, svg, img, video, iframe, embed, object; no padding/border; laid-out width equal to the attribute) has width error 0, so the collapsed space after it (4.45 px at 16 px sans) keeps its fraction: the animation row's svg / svg / video at 64.45 / 128.9 / 193.34 -> 1x columns 64 / 129 / 193, 4x 258 / 516 / 773 (`inline_replaced_width_is_exact`). Spec `inline_replaced_fractional_x_chrome159_spec.spl` (handover from the animation lane, 0/2 -> 2/2). Any other replaced box (percent / CSS / aspect-ratio width) still ends the error chain (unknown).
- **Not done (named):** the letter/edge-space kern on `direction:rtl` runs needs the kern lane's per-edge-pair `Style.resolved_lead_space_milli` / `resolved_trail_space_milli`; `inline_space_kern_nowrap_rtl_chrome159_spec.spl` is tagged in-development (nowrap AC-1 green, rtl AC-2 17 runs off by 1-2 px). The button lane narrows a button only when nothing follows it; once it lands, narrow every button and check the following box is not shifted twice (`button_following_box_x` + `button_label_width` together).

## 2026-11-23 — Engine2D and Skia now compared on the GB10 (native C-string return decode)

- **Result.** On the physical NVIDIA GB10, the native Engine2D and upstream Skia
  Ganesh/Vulkan produce byte-identical pixels for:
  - web-box: `204df3a7…`
  - corpus-case01: `2f4d3fb1…`, which also equals the oracle.

  `run-web-box` and `run-corpus-case01` PASS. corpus-case06 is still blocked:
  the strict Vulkan lane rejects a clipped plain rect
  (`strict-vulkan-command-preflight-required`, Blocker 10).
- **Root cause of "selected Vulkan physical device identity unavailable".** It
  was not the token or the generation; gdb showed `expected_token=2 ==
  get_device=2`. `rt_vulkan_selected_device_identity_v1` returns `*const c_char`.
  The seed's native codegen decodes such returns only for the names in
  `C_STRING_RETURNING_RUNTIME_FNS` (`codegen/instr/calls.rs`), and this symbol
  was missing from that list. `.split(":")` therefore ran on a raw pointer.
  Fixed in the list and in `runtime_sffi.rs`, pinned by
  `cstring_returns_native_decodes_selected_device_identity_v1`.
- **Trap: an extern `-> text` that "works when interpreted, fails native" is
  this class.** Disassemble the facade: `rt_cstring_to_text` must follow the
  call. Whenever a new `-> *const c_char` runtime export lands, re-run the
  census (Rust c_char returners ∩ Simple `-> text` externs). The pure-Simple
  backend has no equivalent list yet.
- **Trap: `cc` on the GB10 host is GCC.** Build the seed with
  `CC=clang CXX=clang++ AR=llvm-ar` and the `clang -fuse-ld=lld` linker, in a
  private `CARGO_TARGET_DIR`.
- **Executable.** Hand-linked, diagnostic-grade (Blocker 8 is unchanged). The
  final binary is `/home/yoon/skia-n2/artifacts/nb_skiadev_20261123/vulkan_2d_qualification_b113785`
  (`98ea91fe…`). With it, `check-skia-web-reference-compare.shs` reports PASS 3/3; that
  script covers the Skia leg only, and `run-*` covers the Engine2D leg. The
  recipe and sha256 are in
  `doc/08_tracking/bug/linux_gb10_n2_qualification_executable_blockers_2026-11-18.md`
  (2026-11-23).

## 2026-11-23: shaped-run spacing — neutrals next to Arabic, glyph xs carry the gaps

- **Re-verified (no change needed):** fractional letter/word-spacing (landed 2026-11-19) — per-glyph first-ink columns at k=1 match Chrome 159 column-for-column for `letter-spacing` 0 / 0.3px / 0.05em / 1.37px and `word-spacing` 2.5px / 0.3px+0.7px. Chrome Range lefts show the pen accumulates the exact float spacing (`0.3px`: 19/64 after 1 char, 38/64 after 2, 57/64 after 3). Fixed-position grayscale text (2026-11-19) spec 5/5.
- **Open, not this lane (k=4):** at device scale 4, glyph pens inside a run sit on whole CSS px (multiples of 4 device px) with or without spacing: `iiii` Chrome 44 59 73 87 101 vs ours 44 60 72 88 100, `letter-spacing:1.37px` up to 3 device px off. The `_lcd_apply_pen_phases` quarter-pen path returns early above 48 device px (grayscale), and `draw_ir_device_scale` multiplies whole-px advances. Same mechanism as `dpr4_word_pen_fraction_chrome159_spec` (wordpen lane).
- **Chrome 159 rule (measured, Range widths at 2px):** a digit or punctuation mark takes the script of the nearest strong letter (before it, else after it); next to Arabic it takes no gap. U+0020 always takes it. `مرحبا123` +0, `مرحبا 123` +2, `123مرحبا` +0, `مرحبا.` +0, `مرحبا!x` +2, `abcمرحبا` +6, `abc123` +12.
- **Change:** `_letter_gap_skipped` (`simple_web_html_layout_renderer_foundation.spl`) resolves those characters for `spaced_advances_milli`. `spaced_glyph_xs_milli` puts the same gaps into a shaped run's glyph xs. Each gap sits right of its codepoint's glyph and moves every glyph further right. `_html_draw_ir_resolved_text_command` applies it. A shaped run with no blank glyph (no space) is painted from xs, so `مرحباabc` at 2px kept its ink (Chrome x1 +4). This was the precondition deva-A named for its empty-glyph skip.
- **Spec:** `shaped_run_spacing_chrome159_spec` AC-7/AC-8, plus AC-9 at device scale 4 (Chrome k=4 `مرحباabc` ink 84..315 -> 84..331; base +0, head +16). 6/9 on base, 9/9 on head.
- **Open defect, seen at k=4:** `simple_web_layout_render_html_pixels_engine2d_at_device_scale` returns an EMPTY frame (len 0) for `<html lang="ar">` with `مرحبا123` (unshaped Arabic+digits). This happens on base too. Chrome paints ink 85..317.
