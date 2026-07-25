# M18: Browser Pseudo-Elements & Text Shaping

## Status: 8/8 tasks done

**Superseded 2026-07-25:** the private fallback module described below had no
remaining caller/export and was retired. Production ownership is now the
canonical semantic browser layout → Draw IR → Engine2D route; the historical
implementation and verification record below is retained for traceability.

| Phase | Status | Detail |
|-------|--------|--------|
| 1-dev | Done | Scoped to ::before/::after, text-overflow, word-break/overflow-wrap |
| 2-research | Done | Fallback renderer pipeline analysis, 6 reusable modules, 7 requirements |
| 3-arch | Done | 2 modules (1 modified, 1 new), 8 decisions, 6 public API functions |
| 4-spec | Done | 8 WPT specs covering AC-1 through AC-4 |
| 5-implement | Superseded | Historical fallback retired; canonical browser layout owns the behavior |
| 6-refactor | Done | No refactoring needed |
| 7-verify | Done | 8/8 new + 57/57 existing WPT tests pass |
| 8-ship | Done | Committed and pushed |

### Deferred to follow-up
1. `@font-face` network loading
2. Bidi/RTL text shaping (UAX #9)
3. Complex script shaping (Arabic, Devanagari)
4. UAX #14/#29 line breaking

## Context

Historically, the browser engine's fallback pixel renderer handled CSS
pseudo-element and text layout support through a simplified div walker. That
unreachable implementation has since been retired; current behavior belongs to
the canonical browser layout and Draw IR path.

### Historical design decisions
- Pseudo-element selector lookup bounded to tag, class, id, and tag+class compound selectors
- `content` parsing handles only CSS quoted string literals; `attr()`/`counter()` return `""`
- `text-overflow: ellipsis` triggers without requiring `overflow: hidden` + `white-space: nowrap` guards (simplified)
- `word-break: break-all` and `overflow-wrap: break-word` treated identically (character-boundary breaks)
- Self-contained `br_draw_block_text()` replaces `FontRenderer` dependency (interpreter can't resolve cross-module static fn calls)

### Bonus fixes
- Parser: added `ui`/`style`/`schema`/`music` domain-block keywords to `expect_path_segment` and `expect_method_name` in `parser_helpers.rs`

## Critical Files

| File | Action | Purpose |
|------|--------|---------|
| `src/lib/gc_async_mut/gpu/browser_engine/html_fallback_renderer.spl` | RETIRED | Unreachable parallel HTML/font renderer removed |
| `test/03_system/feature/web_platform/css/pseudo_text_wpt_spec.spl` | NEW | 8 WPT tests for pseudo-elements and text layout |
| `src/compiler_rust/parser/src/parser_helpers.rs` | MOD | Domain-block keywords in path segments and method names |

## Historical verification

1. `bin/simple test test/03_system/feature/web_platform/css/pseudo_text_wpt_spec.spl` — 8/8 pass
2. `bin/simple test test/03_system/feature/web_platform/css/selector_color_subset_spec.spl` — 57/57 pass (no regression)
3. The former `html_fallback_renderer.spl` check was valid for the historical implementation; the file is now intentionally absent.
4. `bin/simple check test/03_system/feature/web_platform/css/pseudo_text_wpt_spec.spl --source src` — type-check passes
5. `cargo check -p simple-parser` from `src/compiler_rust/` — parser crate check passes
