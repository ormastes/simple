# Blink Render Stack Wiring Plan

Status: PLAN ONLY — no wiring stage landed. See "Why no code landed" below.
Date: 2026-08-11
Scope: `src/lib/blink/**` vs the live lane
(`src/lib/gc_async_mut/gpu/browser_engine/**`, `src/lib/common/ui/**`,
`src/app/ui.browser/**`, `examples/06_io/ui/**`).

## 0. The premise correction (read this first)

The duplication sweep that motivated this work recorded that merging the 8
duplicated families would mean "deleting blink's newer/richer implementations
(e.g. a 20-name colour keyword table) to preserve the weaker live ones
(8-name)", and concluded the fix was to wire blink in.

**That is backwards for the colour family, and for most of the others.**
Measured 2026-08-11:

| | blink | live lane |
|---|---|---|
| named colours | **8** (`cascade.spl:126-140`: transparent, black, white, red, green, blue, yellow, gray/grey) | **~140** (`dom_color.spl:632` `named_color_to_u32`) |
| `rgb()`/`rgba()` | **none** | `dom_color.spl:129` `parse_rgb_unified` |
| `hsl()`/`hsla()` | **none** | `dom_color.spl:475` `parse_hsl_func` |
| `#RRGGBBAA` | **none** (only `#rgb`, `#rrggbb`) | `dom_color.spl:95` `parse_hex_color` |

blink says so itself at `src/lib/blink/style/cascade.spl:36-37`:
"Colors are limited to the named subset below plus `#rgb`/`#rrggbb`; no
`rgb()`/`rgba()`/`hsl()`."

blink is **architecturally cleaner** (a leaf stack: it imports only `blink`,
`skia`, and `common` — no GPU, no `gc_async_mut`) and **better factored**, with
30+ green specs. It is **not** functionally newer. It is a functional SUBSET in
several families. Routing the live lane through blink today would be a
behavioural REGRESSION, not an upgrade.

This reframes the work. It is not "wire blink in". It is **"close blink's gaps,
then wire"** — and the gap-closure is the large half.

## 1. Facts

### 1.1 blink is test-only
`/usr/bin/grep -rn` over `src/` and `examples/` finds exactly ONE production
import of blink:

    src/lib/content/entity/web_contents.spl:7:
      use std.blink.entity.paint_artifact.{PaintArtifact}

Everything else is `test/01_unit/lib/blink/**` and `test/unit/lib/blink/**`.

### 1.2 The live lane's production consumers
These are what a wiring change would have to keep working:

- `src/app/ui.browser/backend.spl:24` `web_render_backend` — reached from
  `src/app/ui/main.spl:14`, `src/app/ui/backend_entry_browser.spl:2`,
  `src/app/cli/browser.spl:14`
- `src/app/browser/render_adapter.spl:21` `render_html_to_pixel_array`
- `src/app/ui.chromium/engine_merge.spl:31-38`
- `src/app/office/gui.spl:51`, `gui_apps.spl:22`, `md_wysiwyg_gui.spl:14`,
  `md_wysiwyg_ppm.spl:14`
- `src/app/llm_caret/gui_metal.spl:5,7`, `src/app/ui_shared_mdi/live_window.spl:6`,
  `src/app/wm_showcase/session.spl:65,68`, `src/app/wm_compare/**`
- **examples/ is LIVE gate source**: `examples/06_io/ui/web_engine2d_gui.spl:18`,
  `web_engine2d_metal_gui.spl:17,19`, `web_render_backend_gui.spl:18`,
  `web_render_dump_ppm.spl:3`, `web_render_file_gui.spl:39`,
  `web_render_page_ppm.spl:12`, `web_standards_showcase_gui.spl:15`,
  `web_text_gui.spl:12`, `wm_fullscreen_metal_gui.spl:38`,
  `examples/09_embedded/simple_os/arch/x86_64/browser_soft_entry.spl:12-14`,
  `gui_entry_desktop.spl:56`
- gate scripts: `scripts/check/check-electron-simple-web-engine2d-bitmap-evidence.shs`,
  `check-electron-simple-web-layout-bitmap-evidence.shs`,
  `check-widget-shells-crossengine-evidence.shs`,
  `check-web-baremetal-size-audit.shs`, `check-gtk-gui-size-speed-baseline.shs`
- two SELF-CONTAINED old engines that share nothing:
  `examples/06_io/ui/mini_html_render.spl`, `examples/06_io/ui/simple_browser.spl`

### 1.3 The 8 duplicated families, with the merge direction
"Direction" = which side is richer, i.e. which implementation survives a merge.

| family | live | blink | direction |
|---|---|---|---|
| hex decode | `dom_color.spl:95` (+6 dups) | `cascade.spl:102` `_hex_digit`, `:113` `_hex_pair` (**private**) | LIVE richer (`#RRGGBBAA`) |
| color parse | `dom_color.spl:8` (+`dom_color_named.spl`) | `cascade.spl:122` `parse_color_value -> SkColor4f` | **LIVE much richer** |
| CSS length | `dom.spl:100` `css_length_px`, `browser_renderer_utils.spl:257` `br_parse_calc_px_i32` | `cascade.spl:74` `parse_length_value -> Length` | LIVE richer (`calc()`) |
| declaration-block split | `style_block_parse.spl:455` `parse_declarations(text)` | only `parse_css(tokens)` — **no raw-string entry** | LIVE has the API blink needs |
| selector specificity | `..._core.spl:2125/2261/2290` | `cascade.spl:291` `_specificity` (**private**) | blink cleaner, private |
| tag tokenizing | `html_tokenizer.spl:353/411` (+3 dups) | `html_parser/tokenizer.spl:32` `tokenize_html` | **blink richer** — full equivalent |
| block-layout advance | `layout_core.spl:60` (+3 dups) | `block_flow.spl:122` `compute_layout()` | LIVE richer (floats, clear, margin-collapse) |
| inline width estimate | `..._layout.spl:290/301/462/492/552` | **MISSING** | LIVE only |

Only ONE family (tag tokenizing) is a clean blink win today.

## 2. BLOCKERS — behaviour blink is MISSING that the live lane has

These are the real gate on wiring. Each must be closed in blink, or explicitly
scoped out, before the corresponding live-lane call site can be re-pointed.

1. **Inline text measurement — entirely absent.** No text-measure API anywhere
   in `src/lib/blink/**`. Live: `simple_web_html_layout_renderer_layout.spl:290`
   `text_advance`, `:301` `style_text_advance`, `:462` `intrinsic_text_width`,
   `:492` `inline_text_advance_width`, `:552` `text_line_advance_width`;
   `html_fallback_renderer.spl:137` `br_char_advance_px`.
   **This alone blocks every pixel-output consumer.**
2. **`rgb()` / `rgba()` / `hsl()` / `hsla()` / `#RRGGBBAA` / ~140 named colours.**
   `cascade.spl:122-158` vs `dom_color.spl:8,95,129,475,632`. blink silently
   resolves all of these to **opaque black** (`cascade.spl:158`) — a wrong
   value, not a failure, so it is invisible to any smoke test.
3. **HTML character-reference decoding. — CLOSED 2026-08-11.**
   `src/lib/common/html/character_references.spl` is the shared decoder;
   `blink/html_parser/tokenizer.spl` calls it for Character-token data and for
   attribute values (the two places WHATWG recognises references), and keeps no
   private table. Named (HTML 4 set plus common typographic/currency/maths/
   arrow/Greek names, case-sensitive), decimal `&#NNN;`, hex `&#xHH;`/`&#XHH;`,
   and the WHATWG-mandated windows-1252 remap of `&#128;`..`&#159;`.
   **Nothing is ever guessed:** unterminated, unknown-name, malformed-numeric
   and out-of-range-numeric each return an explicit `EntityMatch` failure and
   the source text passes through verbatim (`&bogus;` stays `&bogus;`), with
   the reason available via `decode_character_references_checked`. Specs:
   `test/01_unit/lib/common/html/character_references_spec.spl` (23) and
   `test/01_unit/lib/blink/html_tokenizer_entities_spec.spl` (12), both
   mirrored into `test/unit/`.
   The old `common/html/entities.spl` decoder is marked SUPERSEDED in its own
   header (it drops every hex reference and every codepoint >= U+0080, and
   returns an unknown name as bare text) and was left functionally untouched
   for its existing callers; re-pointing them is follow-up work. The live
   lane's `html_tokenizer.spl:588/657` + `html_named_character_references.spl`
   is likewise not yet re-pointed — that is the Stage 1 dedupe half.
4. **Inline `style="..."` parsing. — CLOSED 2026-08-11.**
   `blink/css_parser/parser.spl` now has the raw-string entry points
   `parse_inline_style(source) -> CssDeclarationBlock` and
   `parse_declarations(source) -> [CssDeclaration]`. They do NOT add a second
   reader: the declaration loop was factored out of `parse_css` into
   `_parse_declaration_block`, which both entry points share, so an inline
   style and a rule body cannot disagree about `!important` or about spacing
   inside `calc()`. A malformed declaration (missing `:`, non-identifier
   property, empty value) is dropped AND reported in `errors` rather than
   stored blank. Spec: `test/01_unit/lib/blink/css_inline_style_spec.spl`
   (16), mirrored into `test/unit/`. Live's `style_block_parse.spl:455` is not
   yet re-pointed.
5. **At-rules.** `@media` (`html_string_parser.spl:74-127`,
   `..._core.spl:521-657`, `browser_renderer_utils.spl:279-287`),
   `@supports` (`style/supports.spl:427,444`),
   `@keyframes` + animation (`style_block_parse.spl:66-307`,
   `style/animation.spl:383` `interpolate_color`). blink: none.
6. **Shorthand expansion.** `style_block_parse.spl:572` `expand_shorthand`,
   `:686` `sb_background_shorthand_color_value`, `:727` `expand_box_shorthand`;
   outline `..._declarations.spl:496`. blink: none.
7. **Floats / clear / margin-collapse / tables / containment.**
   `layout_core.spl:132-173`, `layout_float.spl`, `layout_table.spl`,
   `containment.spl:129`. blink `block_flow.spl` is pure block flow only.
8. **`calc()` lengths.** `browser_renderer_utils.spl:257`. blink: none.
9. **Visual effects.** box-shadow `simple_web_css_box_effects.spl:282`,
   `dom_visual_effects.spl`; transforms `style/transform.spl:158`;
   gradients `dom_color_named.spl:37` `parse_linear_gradient`. blink: none.
10. **Style invalidation / rule indexing.** `style_invalidation.spl`,
    `style_rule_index.spl`. blink recascades wholesale.
11. **API surface is private.** blink's `_hex_digit`, `_hex_pair`, `_specificity`
    are `_`-prefixed and unexported, so no external caller can reach them even
    where blink is the better implementation.

## 3. Staged plan

Ordering principle: **every stage that changes blink is zero-production-risk
today** (blink has one production import, `PaintArtifact`, which no stage
touches). All production risk is concentrated in Stage 5+. Do the gap-closure
first; do not re-point a single live call site until Stage 5.

Anti-goal: do NOT reimplement live-lane logic inside blink. That would add a
9th duplicate of colour parsing and make the sweep's finding worse. The
mechanism is Stage 1.

### Stage 1 — shared leaf modules (prerequisite for everything)
Move the richer live implementations DOWN into `src/lib/common/` leaf modules
that both lanes can import. blink imports only `blink`/`skia`/`common` today
and must stay that way — it must never import `gc_async_mut.gpu.**`, which
would drag GPU deps into a leaf stack (and into baremetal).

- **DONE (colour):** `src/lib/common/color/css.spl` — the shared CSS colour
  parser. It landed in the existing `common/color/**` package rather than a new
  `common/css/` one, so it sits beside `types.spl`/`convert.spl` (whose
  `hsl_to_rgb` it reuses) instead of starting an eighth colour package. blink's
  `style/cascade.spl` now imports it and its private nine-colour table is gone.
  Parity with the live lane: 148 CSS Level 4 named colours, `#RGB`/`#RGBA`/
  `#RRGGBB`/`#RRGGBBAA`, `rgb()`/`rgba()`, `hsl()`/`hsla()`, both the legacy
  comma form and the modern space-plus-slash form, percentage channels.
  **Every entry point returns `Color?`.** blink's `parse_color_value` no longer
  answers opaque black for an unsupported colour — the silent wrong pixel that
  hid this whole gap — it answers `nil`, and `apply_declaration` drops the
  invalid declaration as CSS requires. Specs:
  `test/01_unit/lib/common/color/css_color_spec.spl` (25 cases, unsupported
  colours covered explicitly) and the rewritten `parse_color_value` /
  "applying an unsupported colour declaration" blocks of
  `test/01_unit/lib/blink/style_cascade_spec.spl`, both mirrored into
  `test/unit/`. The live lane's `dom_color.spl` is NOT yet re-pointed — that
  half still needs the bitmap-equality proof below.
- `common/css/length.spl` <- `css_length_px` + `br_parse_calc_px_i32`
- `common/css/declarations.spl` <- `style_block_parse.spl:455` `parse_declarations`
- `common/css/entities.spl` <- `html_named_character_references.spl` + decoder

Acceptance: new module's own SSpec is green; the live lane re-points its
imports to `common/css/**` with **byte-identical** behaviour; all live gate
scripts in §1.2 still pass. Reduces the duplicate count from 7 copies of hex
decode / 7+ colour parse to 1 each — this half IS a legitimate dedupe, because
nothing richer is deleted.
Proof: `check-electron-simple-web-engine2d-bitmap-evidence.shs`,
`check-electron-simple-web-layout-bitmap-evidence.shs` (bitmap equality).
Rollback: revert the import re-point; the moved modules are additive.

### Stage 2 — blink consumes the shared leaf; blocker 2, 4, 8 close
Replace `cascade.spl:102-158` (`_hex_digit`, `_hex_pair`, `parse_color_value`)
with delegation to `common/css/color.spl`, converting `u32` ARGB to
`SkColor4f`. Same for `parse_length_value` -> `common/css/length.spl`. Add
`parse_declarations` passthrough so blink can accept inline `style="..."`.
Delete `cascade.spl:36-37`'s limitation note once true.

Acceptance: `test/01_unit/lib/blink/style_cascade_spec.spl` stays **16/16**;
new spec asserts `rgb()`, `rgba()` alpha, `hsl()`, `#RRGGBBAA`, and >=20 named
colours resolve correctly, and that an UNKNOWN colour is distinguishable from
black (blocker 2's silent-black bug).
Rollback: single-file revert of `cascade.spl`; no production caller exists.

### Stage 3 — inline text measurement in blink (blocker 1)
Port `intrinsic_text_width` / `inline_text_advance_width` /
`text_line_advance_width` into `blink/layout/inline_flow.spl` behind the same
font-metric source the live lane uses. This is the single largest blocker and
the one that gates all pixel output.

**LANDED 2026-08-11**, but NOT by porting the live implementation, and the
acceptance criterion below had to change. The measurement landed as a shared
leaf, `src/lib/common/layout/text_metrics.spl`, with blink consuming it through
`src/lib/blink/layout/inline_text.spl`. blink can now measure advance width,
cell width, baseline, line height, and wrap a run into a box.
Proof: `test/01_unit/lib/blink/inline_text_spec.spl` 41/41 PASS (mirrored into
`test/unit/lib/blink/`). `common/spec/evidence/format/terminal_grid.spl` now
delegates its width policy to the same leaf instead of keeping a second copy;
its spec stays 21/21.

Acceptance (AMENDED): the original criterion — "measure the same strings
through both lanes and assert equal advance widths within 1px" — is
UNACHIEVABLE for non-ASCII text and must not be forced. The live lane measures
by UTF-8 BYTE count (`text.len()` is bytes while `char_code_at` is codepoint
indexed), so it over-charges every multi-byte character; see
`doc/08_tracking/bug/live_lane_inline_text_measure_counts_utf8_bytes_2026-08-11.md`.
Cross-lane parity holds for ASCII only until that live defect is fixed, which
is bitmap-gated Stage 1 work. Reintroducing the byte count into blink to force
parity would be a regression.

The three width contracts in the repo (pixel advance, ANSI-stripped visible
columns, terminal cells) are documented at the top of `text_metrics.spl` and are
deliberately NOT unified — the `pad_to_width`/`text_width` ANSI family answers a
different question and merging it in either direction is a behaviour change.
Rollback: additive module; delete it.

### Stage 4 — remaining blink gaps (blockers 3, 5, 6, 7, 9, 10)
Entities, at-rules, shorthands, floats/clear/margin-collapse, effects,
invalidation. Each is independently landable and independently spec'd. Blockers
9 and 10 may legitimately be scoped OUT if the first wired consumer does not
need them — but that must be stated, not assumed.

Acceptance: per-gap SSpec; a parity harness runs the `wm_compare` site corpus
(`src/app/wm_compare/site_corpus_compat.spl:17-19`) through both lanes.

### Stage 5 — re-point ONE consumer (first production risk)
Pick the narrowest, most-instrumented consumer:
`src/app/browser/render_adapter.spl:21` `render_html_to_pixel_array`. Route it
through blink behind a flag defaulting to the OLD lane.

Acceptance: `check-electron-simple-web-layout-bitmap-evidence.shs` passes with
the flag ON; bitmap diff vs the old lane is within the corpus tolerance already
used by `production_gui_web_renderer_parity.spl:15`.
Rollback: flip the flag off. The flag is the rollback story for Stages 5-7 and
must land BEFORE any call site moves.

### Stage 6 — flip the default, keep the flag
Default to blink for the Stage-5 consumer only. Keep the old lane compiled and
reachable for one full release cycle.

### Stage 7 — widen, then retire
Re-point remaining consumers from §1.2 one at a time, each with its own gate
run. Only after ALL consumers are on blink and one cycle has passed may the old
lane be deleted. `examples/06_io/ui/mini_html_render.spl` and `simple_browser.spl`
are self-contained and can be left alone or ported last.

## 4. Rollback story (summary)

- Stages 1-4 touch blink and shared leaves only. blink has ZERO production
  callers besides `PaintArtifact`, so rollback is a file-level revert with no
  production surface.
- Stage 1's live-lane import re-point is the one early production touch; it is
  behaviour-preserving by construction and gated on bitmap-equality evidence.
- Stages 5-7 are gated by a flag that defaults OFF and lands before any call
  site moves. Rollback is a flag flip, not a revert.
- The old lane is not deleted until Stage 7 completes plus one release cycle.

## 5. Why no code landed with this plan

Every stage that changes blink is safe, and the per-file spec gate DOES run:

    bin/simple test test/01_unit/lib/blink/style_cascade_spec.spl
    -> SPEC FILE VERDICT: ... executed=16 passed=16 failed=0 / PASS

(Note the runner's directory lane emits NO verdict lines for
`test/01_unit/lib/blink` — see `src/app/test_runner_new/test_runner_main.spl:931`.
Gate per FILE, never per directory, or the run is fail-open.)

But Stage 2 — the smallest real behaviour change — is only correct ON TOP of
Stage 1. Doing Stage 2 first would mean reimplementing colour parsing inside
blink, creating a 9th duplicate of the exact family the sweep refused to touch,
and would have to be undone by Stage 1 immediately after. Stage 1 itself is not
the safest stage: it re-points live-lane imports and its acceptance evidence is
the Electron bitmap gates, which are not a per-file spec run.

So the honest first step is Stage 1, and Stage 1 is not safe to do blind.
Landing this plan without code is the correct outcome.

## 6. Notes for whoever picks this up

- `/usr/bin/grep -rn` — the wrapped `grep` honours `.gitignore` and
  UNDER-REPORTS. `examples/` is LIVE gate source and must be in every sweep.
- Any new spec must be mirrored into BOTH `test/01_unit/lib/blink/` and
  `test/unit/lib/blink/` or `check-test-tree-divergence.shs` fails.
- No wrong oracle was found in the blink specs for the colour family — they
  simply do not cover unsupported colours at all, which is how blocker 2's
  silent-black bug stayed invisible. Stage 2's new spec must cover it.
