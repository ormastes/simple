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
- [ ] 2-research (Analyst)
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
<pending>

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
