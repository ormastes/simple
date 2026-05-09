# Browser Engine Implementation Guide

The Simple browser engine is a GPU-accelerated HTML/CSS renderer in the canonical engine at `src/lib/gc_async_mut/gpu/browser_engine/`. It targets Chromium-class rendering fidelity through incremental milestone delivery.

**Status**: M13 complete (float layout + CSS quick wins). 132/132 corpus pixel-exact. WPT ~49-54%.

## Source Files

| File | Purpose |
|------|---------|
| `src/lib/gc_async_mut/gpu/browser_engine/layout.spl` | Layout engine: block, flex, float, text |
| `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` | DOM tree, style parsing, event dispatch |
| `src/lib/gc_async_mut/gpu/browser_engine/css.spl` | CSS types (StyleProps, CssValue, FloatCode, ClearCode) |
| `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` | Paint/render pipeline |
| `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl` | CSS cascade, shorthand expansion |
| `src/lib/gc_async_mut/gpu/browser_engine/html_parser.spl` | HTML tokenizer and tree builder |

## Architecture

```
HTML string
  -> html_parser.spl    (tokenize + tree-build -> BeDomNode tree)
  -> dom.spl            (set_style per node, cascade)
  -> layout.spl         (layout_tree -> BeLayoutBox tree)
  -> browser_renderer.spl (paint BeLayoutBox -> SceneCommand list -> GPU)
```

Per ADR-002, this canonical engine is production. The research tree at `examples/browser/` is demoted to labs.

## Layout Engine

### Entry Point

`layout_tree(root, viewport_w, viewport_h) -> BeLayoutBox` creates a root FloatContext and dispatches to `layout_node`.

### Display Dispatch (layout_node)

| Display value | Handler |
|---------------|---------|
| `"none"` | Returns empty BeLayoutBox |
| `"flex"`, `"inline-flex"` | `layout_flex` |
| `"flow-root"` | `layout_block` (BFC auto-detected) |
| text node | `layout_text_node` |
| everything else | `layout_block` |

### Float Layout (M13)

Float layout follows CSS 2.1 section 9.5.1. Key types in `layout.spl`:

- **FloatBox** — positioned float with `x, y, width, height, side` (i32 geometry, side: 1=left 2=right)
- **FloatContext** — tracks `left_floats: [FloatBox]`, `right_floats: [FloatBox]`, `current_y: i32`
- **FloatPos** — return type for placement: `x, y`

Float utility functions:

| Function | Purpose |
|----------|---------|
| `float_available_width_at(y, ctx, total_width)` | Available width minus float intrusions at y |
| `float_left_offset_at(y, ctx)` | Left edge offset from left floats at y |
| `float_clear_y(clear_code, ctx)` | Y after clearing (1=left 2=right 3=both) |
| `float_place(w, h, side, ctx, container_w)` | Place a float, advancing down if no room |
| `float_context_height(ctx)` | Max bottom of all floats (for BFC containment) |

### Block Formatting Context (BFC)

BFC roots get a fresh FloatContext. Detected by:
- `overflow != "visible"` (hidden, auto, scroll)
- `display: flow-root`, `display: flex`, `display: inline-flex`
- Document root (layout_tree creates top-level BFC)

BFC roots expand their height to contain all floats via `float_context_height`.

### Float-Aware Child Loop (layout_block)

For each child in a block container:
1. Check `child_style.clear_code` — if > 0, advance cursor_y past cleared floats
2. Check `child_style.float_code` — if 1 or 2, lay out child, place via `float_place`, register in FloatContext, do NOT advance cursor_y
3. Otherwise (normal flow): narrow container by float intrusions at cursor_y (fast-path skips when no floats exist)

### Text Wrapping Around Floats (layout_text_node)

When FloatContext has active floats, text layout switches to per-line mode:
- Each line queries `float_available_width_at(line_y, ctx, container_width)` for available width
- Characters per line computed from available width and char width
- Fast path: when no floats exist, uses the original ceiling formula (preserves 132-corpus pixel parity)

### Performance Notes

Float context is threaded through all layout functions as a parameter (reference semantics verified). Performance-critical optimizations:
- Direct `i32` field access for `float_code`/`clear_code` (no wrapper object allocation)
- Fast-path guard: `float_available_width_at`/`float_left_offset_at` skipped when float lists are empty
- BFC detection inlined to avoid per-block function call overhead
- Flex children reuse parent FloatContext instead of allocating fresh empty contexts

## CSS Quick Wins (M13)

| Feature | Status | Location |
|---------|--------|----------|
| `hsl()`/`hsla()` | Already implemented | `dom.spl:parse_hsl_func` |
| `currentColor` | Implemented | `dom.spl` — background-color, border-color, outline-color |
| `display: inline-flex` | Implemented | `layout.spl:layout_node` dispatches to `layout_flex` |
| `display: flow-root` | Implemented | `layout.spl:layout_node` dispatches to `layout_block` (BFC auto-detected) |
| `list-style: none` | Already works | Engine renders no list markers |
| `flex-flow` shorthand | Already implemented | `style_block.spl` expands to flex-direction + flex-wrap |
| `calc()` arithmetic | Already implemented | `css.spl:css_resolve_calc_px` handles +,-,*,/ for px |

## Testing

```bash
# 132-page corpus regression gate (must remain pixel-exact)
bin/simple test test/sys/wm_compare/famous_site_corpus_spec.spl

# Same, cache-busted (use after layout changes)
bin/simple test test/sys/wm_compare/famous_site_corpus_spec.spl --clean

# Float layout unit tests
bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/float_layout_spec.spl

# CSS routing tests
bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/css_ext_routing_spec.spl

# All browser engine tests
bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/

# Enable layout debug output
SIMPLE_DEBUG_LAYOUT=1 bin/simple run <script.spl>
```

## Milestone History

| Milestone | Gate | Status |
|-----------|------|--------|
| M1-M12 | 132/132 corpus, Acid2, 30/30 design effects | Complete |
| M13 | Float layout, CSS quick wins, 132-corpus regression | Complete (AC-7 WPT waived) |
| M14+ | See `doc/03_plan/simple_browser_chrome_class_roadmap.md` | Planned |

## References

- [Chrome-class roadmap M13-M24](../03_plan/simple_browser_chrome_class_roadmap.md)
- [ADR-002: Canonical Browser Engine](../04_architecture/adr/ADR-002-canonical-browser-engine.md)
- [CSS 2.1 Float Specification](https://www.w3.org/TR/CSS2/visuren.html#floats)
- [M13 SStack state](.sstack/m13-float-css-quickwins/state.md)
