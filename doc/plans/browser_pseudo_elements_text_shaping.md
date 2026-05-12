# M18: Browser Pseudo-Elements & Text Shaping

## Status: 8/8 tasks done

| Phase | Status | Detail |
|-------|--------|--------|
| 1-dev | Done | Scoped to ::before/::after, text-overflow, word-break/overflow-wrap |
| 2-research | Done | Fallback renderer pipeline analysis, 6 reusable modules, 7 requirements |
| 3-arch | Done | 2 modules (1 modified, 1 new), 8 decisions, 6 public API functions |
| 4-spec | Done | 8 WPT specs covering AC-1 through AC-4 |
| 5-implement | Done | Self-contained block text renderer in html_fallback_renderer.spl |
| 6-refactor | Done | No refactoring needed |
| 7-verify | Done | 8/8 new + 57/57 existing WPT tests pass |
| 8-ship | Done | Committed and pushed |

### Deferred to follow-up
1. `@font-face` network loading
2. Bidi/RTL text shaping (UAX #9)
3. Complex script shaping (Arabic, Devanagari)
4. UAX #14/#29 line breaking

## Context

The browser engine's fallback pixel renderer needed CSS pseudo-element and text layout support. The fallback renderer (`html_fallback_renderer.spl`) is a simplified div-walker that reads CSS via text scanning, not `StyleProps`. All new helpers are self-contained in the fallback path with no cross-module class dependencies, ensuring interpreter compatibility.

### Key design decisions
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
| `src/lib/gc_async_mut/gpu/browser_engine/html_fallback_renderer.spl` | MOD | 6 new helpers + integration in `br_render_simple_block_fallback_pixels` |
| `test/web_platform/css/pseudo_text_wpt_spec.spl` | NEW | 8 WPT tests for pseudo-elements and text layout |
| `src/compiler_rust/parser/src/parser_helpers.rs` | MOD | Domain-block keywords in path segments and method names |

## Verification

1. `bin/simple test test/web_platform/css/pseudo_text_wpt_spec.spl` — 8/8 pass
2. `bin/simple test test/web_platform/css/selector_color_subset_spec.spl` — 57/57 pass (no regression)
3. `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/html_fallback_renderer.spl --source src` — type-check passes
4. `bin/simple check test/web_platform/css/pseudo_text_wpt_spec.spl --source src` — type-check passes
5. `cargo check -p simple-parser` from `src/compiler_rust/` — parser crate check passes
