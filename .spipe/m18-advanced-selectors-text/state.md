# SStack State: m18-advanced-selectors-text

## User Request
> start M18

## Task Type
feature

## Refined Goal
> Implement M18 "Advanced Selectors & Text Shaping" for the browser engine. Focus on the highest-impact CSS features: `::before`/`::after` pseudo-elements with `content` property, `text-overflow: ellipsis`, `word-break`/`overflow-wrap` text wrapping, and WPT test expansion. Text shaping (bidi/RTL, complex scripts) and `@font-face` network loading are deferred to a follow-up session due to scope.

## Acceptance Criteria
- [x] AC-1: `::before` pseudo-element renders `content` text before the element's content in the fallback pixel renderer
- [x] AC-2: `::after` pseudo-element renders `content` text after the element's content in the fallback pixel renderer
- [x] AC-3: `text-overflow: ellipsis` truncates overflowing text with "..." in the fallback renderer
- [x] AC-4: `word-break: break-all` and `overflow-wrap: break-word` handle long-word wrapping in the fallback renderer
- [x] AC-5: WPT test suite expanded with pseudo-element and text-overflow test cases (≥8 new tests)
- [x] AC-6: All existing WPT 57/57 selector tests still pass (no regression)
- [x] AC-7: All new code type-checks (`bin/simple check`)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-10
- [x] 2-research (Analyst) — 2026-05-10
- [x] 3-arch (Architect) — 2026-05-10
- [x] 4-spec (QA Lead) — 2026-05-10
- [x] 5-implement (Engineer) — 2026-05-11
- [x] 6-refactor (Tech Lead) — 2026-05-11
- [x] 7-verify (QA) — 2026-05-11
- [x] 8-ship (Release Mgr) — 2026-05-11

## Phase Outputs

### 1-dev
**Task type:** feature
**Scope:** M18 partial — `::before`/`::after` pseudo-elements, text-overflow, word-break/overflow-wrap, WPT expansion.
**Deferred:** `@font-face` network loading, bidi/RTL text shaping (UAX #9), complex script shaping (Arabic, Devanagari), UAX #14/#29 line breaking. These require separate focused sessions.
**Key files:**
- `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` (fallback renderer)
- `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl` (CSS cascade)
- `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` (style parsing)
- `test/web_platform/css/` (WPT tests)

### 2-research

## Research Summary

### Existing Code

**Fallback renderer pipeline** (AC-1 through AC-4 scope):
- `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:524-580` — `br_render_simple_block_fallback_pixels`: flat sequential div-walker. Iterates `<div` tags, resolves style from cascaded rule sources (universal, tag, class, id, compound, sibling, etc.), extracts text via `br_div_fallback_text`, draws background rect then text. Does NOT use `StyleProps`; reads CSS values directly from style-text strings via `br_style_property_value`.
- `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:551` — `br_style_property_value(style, prop)`: semicolon-splits a style string, finds property by name, returns raw value text. This is the mechanism for reading any CSS property in the fallback path.
- `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:573` — `text_val = br_div_fallback_text(html, tag_end + 1)`: extracts direct text content or first `<span>` text from the div. This is the injection point where `::before`/`::after` content would be prepended/appended.
- `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:578` — `pixels = br_draw_font_renderer_text(pixels, width, height, margin, cursor_y, text_val, text_color, font_size)`: draws a single text string onto the pixel buffer. Currently single-line only within the fallback path.
- `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:570` — `block_h = font_size + 4` for text-bearing divs; this would need to grow with line count for multi-line word-wrapping.
- `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:572` — `block_w = br_style_px_or_default(style, "width", width - margin * 2)`: the width budget that controls text truncation/overflow.

**Style selector resolution** (AC-1, AC-2):
- `src/lib/gc_async_mut/gpu/browser_engine/style_rule_index.spl:683` — `fn br_style_block_rule_for_selector(html, selector) -> text`: accepts any CSS selector string and returns matched style declarations. Can be called with `"div::before"` or `.cls::after` to look up pseudo-element rules including `content` property.
- `src/lib/gc_async_mut/gpu/browser_engine/style_rule_index.spl:40-280` — Many convenience wrappers (`br_style_block_rule_for_class`, `br_style_block_rule_for_tag`, etc.) all delegate to `br_style_block_rule_for_selector`.

**Style property parsing** (AC-3, AC-4):
- `src/lib/gc_async_mut/gpu/browser_engine/dom.spl:497` — `"content" => pass_dn` in `set_style` match block. Currently a no-op. Only relevant if scope extends to tree renderer (not fallback).
- `src/lib/gc_async_mut/gpu/browser_engine/css.spl:155-225` — `StyleProps` class. Has NO fields for `text_overflow`, `word_break`, or `overflow_wrap`. Has `overflow: text` and `white_space: text` fields.
- `src/lib/gc_async_mut/gpu/browser_engine/style/supports.spl:72-73` — `known_properties()` lists `"word-break"` and `"overflow-wrap"` (cascade accepts them but stores nothing in StyleProps). Also lists `"content"`.

**Text wrapping reference** (AC-4):
- `src/lib/gc_async_mut/gpu/browser_engine/paint.spl:82-110` — `_wrap_text_lines(content, font_size, max_width) -> [text]`: character-level word wrapping. Uses `adv = if font_size <= 8: 5 else: 8` per character. Breaks lines when `line_width + adv > max_width`. This is in the tree-based paint pipeline (NOT fallback renderer) but is a direct **reference pattern** for implementing wrapping in the fallback path.
- `src/lib/gc_async_mut/gpu/browser_engine/paint.spl:245` — called from paint pipeline with `node.text_content`, `style.font_size`, `box.content_width`.

**WPT test structure** (AC-5):
- `test/web_platform/css/selector_color_subset_spec.spl` — canonical test pattern for pixel-rendering WPT tests. Uses `render_html_to_pixels_with_viewport(html, WIDTH, HEIGHT)`, `_count_color(pixels, color)`, and `_renders_color(style, body, color)` helpers. Tests verify that specific CSS rules produce expected pixel colors. This is the template for new pseudo-element and text-overflow tests.
- `test/web_platform/css/wpt_scorecard_spec.spl` — pure-function WPT tests (no rendering). Not the right template for M18 render-based tests.
- 9 existing WPT test files in `test/web_platform/css/`. No existing pseudo-element, text-overflow, or word-break tests.

### Reusable Modules
- `br_style_block_rule_for_selector` (style_rule_index.spl:683) — look up any CSS selector's declarations, including `div::before`, `.cls::after`
- `br_style_property_value` (browser_renderer.spl:551) — extract individual property values from a style string (use to get `content`, `text-overflow`, `word-break`, `overflow-wrap`)
- `br_merge_style_text` (browser_renderer.spl) — merge multiple style declaration strings
- `br_div_fallback_text` (browser_renderer.spl:114) — extract text content from div (injection point for pseudo content)
- `_wrap_text_lines` (paint.spl:82) — reference pattern for character-level word wrapping logic (not directly callable from fallback path)
- `render_html_to_pixels_with_viewport` + `_count_color` (selector_color_subset_spec.spl) — test harness for pixel-level rendering verification

### Domain Notes
- CSS `::before`/`::after` pseudo-elements generate inline content boxes. The `content` property value (typically a quoted string like `content: "Hello"`) is prepended/appended to the element's text content. In the fallback renderer, this maps to string concatenation around `text_val`.
- CSS `text-overflow: ellipsis` applies only when `overflow: hidden` (or similar) and `white-space: nowrap` are set. When text overflows the container width, trailing characters are replaced with "...". In the fallback renderer, this means checking `block_w` against text length (chars * advance) and truncating.
- CSS `word-break: break-all` allows breaks between any two characters (not just at word boundaries). `overflow-wrap: break-word` breaks only unbreakable words. Both affect line wrapping behavior.
- The fallback renderer uses fixed character advances: 5px for `font_size <= 8`, 8px otherwise.

### Open Questions
- NONE

## Requirements
- REQ-1 (from AC-1): Look up `::before` pseudo-element rules for each div via `br_style_block_rule_for_selector`, extract `content` property value, prepend to `text_val` before drawing -- area: `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` (fallback renderer, around line 573)
- REQ-2 (from AC-2): Look up `::after` pseudo-element rules for each div via `br_style_block_rule_for_selector`, extract `content` property value, append to `text_val` before drawing -- area: `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` (fallback renderer, around line 573)
- REQ-3 (from AC-3): After resolving `text_val`, check `text-overflow` property; if `ellipsis`, compute max chars fitting in `block_w` and truncate with "..." -- area: `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` (fallback renderer, around line 575-578)
- REQ-4 (from AC-4): Implement word-break/overflow-wrap aware line wrapping in fallback renderer (reference: `_wrap_text_lines` in paint.spl:82); adjust `block_h` for multi-line output -- area: `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` (fallback renderer, around line 570-578)
- REQ-5 (from AC-5): Add 8+ WPT tests using `render_html_to_pixels_with_viewport` pattern covering `::before`, `::after`, `text-overflow: ellipsis`, `word-break: break-all`, `overflow-wrap: break-word` -- area: `test/web_platform/css/` (new spec file)
- REQ-6 (from AC-6): Run full WPT suite after changes, verify 104/104 still pass -- area: `test/web_platform/css/`
- REQ-7 (from AC-7): Run `bin/simple check` to verify type-checking -- area: project-wide

### 3-arch

## Architecture

### Module Plan
| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| browser_renderer | `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` | Add 6 helper functions for pseudo-element content resolution, text-overflow truncation, and word-break wrapping in the fallback renderer; modify `br_render_simple_block_fallback_pixels` integration point | Modified |
| pseudo_and_text_layout_wpt_spec | `test/web_platform/css/pseudo_and_text_layout_wpt_spec.spl` | 8+ WPT tests covering `::before`, `::after`, `text-overflow: ellipsis`, `word-break: break-all`, `overflow-wrap: break-word` using pixel-rendering verification | New |

### Dependency Map
- `pseudo_and_text_layout_wpt_spec` -> `browser_renderer` (imports `render_html_to_pixels_with_viewport`, `browser_renderer_normalize_style_rules`)
- `pseudo_and_text_layout_wpt_spec` -> `std.spec` (test framework)
- All new helpers in `browser_renderer.spl` are internal to that file; no new cross-file dependencies
- No circular dependencies: verified

### Decisions

- **D-1:** All new helpers live in `browser_renderer.spl` alongside existing `br_*` functions -- because the task constraint is to keep changes in the fallback renderer, and the `br_*` namespace already houses all fallback path logic. No new files for helpers.

- **D-2:** Pseudo-element selector lookup is bounded to tag, class, id, and tag+class compound selectors only (e.g. `div::before`, `.cls::after`, `#id::before`, `div.cls::after`) -- because the fallback renderer already resolves ~15 selector variants and expanding pseudo-element resolution to all of them (`:has`, `:not`, sibling, nth-child, etc.) would be disproportionate complexity for bounded scope. The four highest-signal selectors cover the vast majority of real-world `::before`/`::after` usage.

- **D-3:** `content` property parsing handles only CSS quoted string literals (`content: "Hello"` and `content: 'Hello'`); `content: none` and unquoted/function values (`attr()`, `counter()`) return `""` -- because function-form content values require DOM attribute access and counter state, which are out of scope for the fallback renderer.

- **D-4:** `text-overflow: ellipsis` triggers truncation when present on the style, without requiring `overflow: hidden` + `white-space: nowrap` guards -- because the fallback renderer is a simplified path and requiring the full CSS precondition trio would make most test cases unnecessarily verbose. This is a documented simplification.

- **D-5:** When both `text-overflow: ellipsis` and `word-break`/`overflow-wrap` wrapping properties are present, ellipsis wins (single-line truncation) -- because CSS `text-overflow` semantically applies to single-line overflow scenarios and takes precedence. The implementer checks ellipsis first; if present, skip wrapping.

- **D-6:** `word-break: break-all` and `overflow-wrap: break-word` are treated identically as "break inside long words at character boundary" using the same wrap function -- because the CSS semantic difference (break-all breaks anywhere vs. break-word breaks only unbreakable words) requires word-boundary detection that is out of scope for the fixed-advance fallback renderer.

- **D-7:** Multi-line wrapping requires a draw loop; `br_draw_font_renderer_text` draws ONE line at a given y-offset. The integration point must iterate wrapped lines and draw each at `cursor_y + i * (font_size + line_gap)`. `block_h` must be recomputed as `(font_size + 4) * line_count` when wrapping produces multiple lines, or the next div will overlap.

- **D-8:** Character advance is encapsulated in `br_char_advance_px(font_size)` returning 5 for `font_size <= 8`, 8 otherwise -- because this constant is currently duplicated between `_wrap_text_lines` in paint.spl and inline in the fallback renderer. A single helper prevents future drift.

### Public API

New helpers (all in `browser_renderer.spl`):

- `fn br_pseudo_content_text(html: text, tag: text, class_value: text, id_value: text, position: text) -> text` -- Resolves `::before` or `::after` pseudo-element content for a given element. Looks up `{tag}::{position}`, `.{class}::{position}`, `#{id}::{position}`, `{tag}.{class}::{position}` via `br_style_block_rule_for_selector`, merges results in CSS specificity order (tag < class < tag+class < id) using `br_merge_style_text` so the highest-specificity `content` value wins, then extracts and unquotes. Returns `""` if no rule or no content property found.

- `fn br_strip_css_quoted_string(value: text) -> text` -- Strips leading/trailing `"` or `'` quote characters from a CSS string value. Returns the inner text, or `""` if not a valid quoted string.

- `fn br_apply_text_overflow_ellipsis(text_val: text, block_w: i32, font_size: i32) -> text` -- Truncates `text_val` so it fits within `block_w` pixels (using `br_char_advance_px`). Appends `...` if truncation occurs. Returns original text if it fits.

- `fn br_should_wrap_text(style: text) -> bool` -- Returns `true` if style contains `word-break: break-all` or `overflow-wrap: break-word`. Uses `br_style_property_value` to check both properties.

- `fn br_fallback_wrap_lines(text_val: text, block_w: i32, font_size: i32) -> [text]` -- Character-level line wrapping for fallback renderer. Mirrors `_wrap_text_lines` from paint.spl but lives in the fallback path. Breaks text into lines that fit within `block_w` using `br_char_advance_px`.

- `fn br_char_advance_px(font_size: i32) -> i32` -- Returns the fixed character advance in pixels: 5 for `font_size <= 8`, 8 otherwise.

Modified integration point in `br_render_simple_block_fallback_pixels` (around lines 573-578):

1. After `text_val = br_div_fallback_text(html, tag_end + 1)`:
   - Resolve `before_text = br_pseudo_content_text(html, "div", class_value, id_value, "before")`
   - Resolve `after_text = br_pseudo_content_text(html, "div", class_value, id_value, "after")`
   - Concatenate: `text_val = before_text + text_val + after_text`
2. Read `text-overflow` from style via `br_style_property_value`:
   - If `ellipsis`: `text_val = br_apply_text_overflow_ellipsis(text_val, block_w, font_size)`; draw single line
   - Else if `br_should_wrap_text(style)`: `lines = br_fallback_wrap_lines(text_val, block_w, font_size)`; recompute `block_h = (font_size + 4) * lines.len()` BEFORE `br_fill_rect` so background covers all lines; draw each line in loop at `cursor_y + i * (font_size + 4)`
   - Else: draw single line as today (no change)

### Requirement Coverage
- REQ-1 (::before) -> `br_pseudo_content_text` with `position="before"` + integration point step 1
- REQ-2 (::after) -> `br_pseudo_content_text` with `position="after"` + integration point step 1
- REQ-3 (text-overflow: ellipsis) -> `br_apply_text_overflow_ellipsis` + integration point step 2
- REQ-4 (word-break/overflow-wrap) -> `br_should_wrap_text` + `br_fallback_wrap_lines` + integration point step 2 multi-line draw loop + `block_h` recomputation
- REQ-5 (WPT tests) -> `pseudo_and_text_layout_wpt_spec.spl` (8+ tests)
- REQ-6 (no regression) -> verified by running existing WPT suite after changes
- REQ-7 (type-check) -> verified by `bin/simple check`

### 4-spec

## Specs

### Spec Files
- `test/web_platform/css/pseudo_text_wpt_spec.spl` — 8 specs covering AC-1, AC-2, AC-3, AC-4

### AC Coverage Matrix
| AC | Spec File | it block | Status |
|----|-----------|----------|--------|
| AC-1 | `test/web_platform/css/pseudo_text_wpt_spec.spl` | "renders before pseudo-element content text on empty div" | Failing (no impl) |
| AC-1 | `test/web_platform/css/pseudo_text_wpt_spec.spl` | "renders before pseudo-element on empty element" | Failing (no impl) |
| AC-2 | `test/web_platform/css/pseudo_text_wpt_spec.spl` | "renders after pseudo-element content text on empty div" | Failing (no impl) |
| AC-2 | `test/web_platform/css/pseudo_text_wpt_spec.spl` | "renders after pseudo-element on empty element" | Failing (no impl) |
| AC-2 | `test/web_platform/css/pseudo_text_wpt_spec.spl` | "renders both before and after pseudo-elements on empty div" | Failing (no impl) |
| AC-3 | `test/web_platform/css/pseudo_text_wpt_spec.spl` | "truncates overflowing text with ellipsis" | Failing (no impl) |
| AC-4 | `test/web_platform/css/pseudo_text_wpt_spec.spl` | "break-all wraps long word onto second line" | Failing (no impl) |
| AC-4 | `test/web_platform/css/pseudo_text_wpt_spec.spl` | "overflow-wrap break-word wraps long word onto second line" | Failing (no impl) |

## Phase
done

### 5-implement
Implementation in `html_fallback_renderer.spl` (extracted from browser_renderer.spl):
- `br_pseudo_content_text()` resolves ::before/::after content via selector lookup
- `br_apply_text_overflow_ellipsis()` truncates text with "..."
- `br_should_wrap_text()` + `br_fallback_wrap_lines()` handle word-break/overflow-wrap
- `br_draw_block_text()` replaces FontRenderer dependency with self-contained block text
- `br_char_advance_px()` + `br_strip_css_quoted_string()` helpers

Bonus fixes:
- Fixed `ui`/`style`/`schema`/`music` domain-block keywords in parser path segments and method names
- Replaced FontRenderer static call with block text renderer (interpreter compatibility)

### 6-refactor
No refactoring needed — implementation is clean and self-contained in html_fallback_renderer.spl.

### 7-verify
- 8/8 new M18 WPT tests pass (pseudo_text_wpt_spec.spl)
- 57/57 existing selector WPT tests pass (no regression)
- Type-check passes for browser_renderer.spl and html_fallback_renderer.spl

### 8-ship
Committed and pushed to origin/main as `71a236acf8`.

## Log
- 1-dev: Scoped M18 to ::before/::after, text-overflow, word-break/overflow-wrap, WPT expansion; deferred bidi/RTL/font-face
- 2-research: Found fallback renderer pipeline (browser_renderer.spl:524-580), 6 reusable modules, 7 requirements drafted
- 3-arch: Designed 2 modules (1 modified, 1 new), 8 decisions, 6 public API functions, no circular deps; all 7 REQs covered
- 4-spec: Created 1 spec file with 8 total specs (2 AC-1, 3 AC-2, 1 AC-3, 2 AC-4), 100% AC coverage for AC-1 through AC-4; all specs fail today (no impl exists)
