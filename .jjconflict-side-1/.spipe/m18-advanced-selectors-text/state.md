# SStack State: m18-advanced-selectors-text

## User Request
> start M18

## Task Type
feature

## Refined Goal
> Implement M18 "Advanced Selectors & Text Shaping" for the browser engine. Focus on the highest-impact CSS features: `::before`/`::after` pseudo-elements with `content` property, `text-overflow: ellipsis`, `word-break`/`overflow-wrap` text wrapping, and WPT test expansion. Text shaping (bidi/RTL, complex scripts) and `@font-face` network loading are deferred to a follow-up session due to scope.

## Acceptance Criteria
- [ ] AC-1: `::before` pseudo-element renders `content` text before the element's content in the fallback pixel renderer
- [ ] AC-2: `::after` pseudo-element renders `content` text after the element's content in the fallback pixel renderer
- [ ] AC-3: `text-overflow: ellipsis` truncates overflowing text with "..." in the fallback renderer
- [ ] AC-4: `word-break: break-all` and `overflow-wrap: break-word` handle long-word wrapping in the fallback renderer
- [ ] AC-5: WPT test suite expanded with pseudo-element and text-overflow test cases (≥8 new tests)
- [ ] AC-6: All existing WPT 104/104 tests still pass (no regression)
- [ ] AC-7: All new code type-checks (`bin/simple check`)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-10
- [x] 2-research (Analyst) — 2026-05-10
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

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
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
