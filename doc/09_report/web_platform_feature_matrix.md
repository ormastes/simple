# Web Platform Feature Matrix

Date: 2026-05-06

Scope: Simple browser renderer compatibility evidence for HTML, CSS, DOM/rendering, and browser-facing host behavior. Status values are `supported`, `partial`, `missing`, and `not-applicable`.

## DOM And Rendering

| Feature | Status | Evidence | Notes |
| --- | --- | --- | --- |
| Browser DOM events | partial | `src/lib/gc_async_mut/gpu/browser_engine/dom.spl`; `src/lib/gc_async_mut/gpu/browser_engine/layout.spl`; `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl`; `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl` | Simplified `BeDomNode` listener registration, event-name normalization, inline `on...` handler discovery, lightweight Event state (`type`, `target`, `currentTarget`, `bubbles`, `cancelable`, `defaultPrevented`, propagation stop flags), deterministic capture/target/bubble ordering, first-match tree path discovery by target id, layout-box coordinate hit-test routing to root-to-target pointer/click dispatch, deterministic mousedown/up sequencing with click synthesis only when both phases hit the same target, focused default-action metadata, cancelable default suppression, simplified returned-node default effects for checkbox/radio/focus/button/form/navigation tokens, disabled control default suppression, focused Enter/Space keyboard activation mapping to click/default effects for common interactive elements, and deterministic `stop-propagation` / `stop-immediate-propagation` listener-token behavior are covered. Executable JavaScript listener callbacks, composed paths, shadow DOM retargeting, real PointerEvent/MouseEvent payload fields, pointer capture, full keyboard event dispatch, async event-loop delivery, and document-wide default-action side effects remain unsupported. |
| CSS selector-list pseudos | partial | `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl`; `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`; `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`; `doc/09_report/chrome_modern_web_platform_compat_2026-05-06.md` | Covers fallback-renderer matching for `:is()`, `:where()`, tag-qualified functional pseudos, simple `:not()` selector-list exclusion, and simple descendant `:has()` with comma-safe selector-list splitting. Complex relative selectors, sibling combinators, specificity parity, and WPT completeness are not claimed. |
| CSS attribute selectors | partial | `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl`; `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`; `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`; `test/web_platform/css/selector_color_subset_spec.spl` | Covers `[attr]` presence, `[attr=value]` exact matching, and bounded `[attr^=value]`, `[attr*=value]`, `[attr~=value]` operators, including tag-qualified exact/prefix selectors in the fallback renderer. Dash-match, namespaces, case-sensitivity flags, escaping, quoted whitespace edge cases, and full selector specificity parity are not claimed. |
| CSS layer blocks | partial | `src/lib/gc_async_mut/gpu/browser_engine/style_block.spl`; `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl`; `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`; `test/web_platform/css/selector_color_subset_spec.spl` | Flattens simple `@layer name { ... }` wrappers so existing selector/declaration scans can apply nested rules. Cascade-layer ordering, layer precedence, anonymous layers, imports, media interactions, and full CSS Cascade Level 5 semantics are not claimed. |
| WPT selector/color subset | partial | `tools/wpt_to_sspec/README.md`; `doc/03_plan/sys_test/wpt_subset_migration.md`; `test/web_platform/css/selector_color_subset_spec.spl` | Adds the first executable 31-case WPT-shaped subset for deterministic selector and color/background pixel behavior. This is a curated subset, not a complete WPT importer or conformance claim. |

## Verification

Required focused commands after DOM event work:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/dom.spl test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl --mode=interpreter --clean`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl --mode=interpreter --clean`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --mode=interpreter --clean`
- `bin/simple test test/web_platform/css/selector_color_subset_spec.spl --mode=interpreter --clean`
- `bin/simple check src/lib`
