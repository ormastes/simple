# Web Platform Feature Matrix

Date: 2026-05-06

Scope: Simple browser renderer compatibility evidence for HTML, CSS, DOM/rendering, and browser-facing host behavior. Status values are `supported`, `partial`, `missing`, and `not-applicable`.

## DOM And Rendering

| Feature | Status | Evidence | Notes |
| --- | --- | --- | --- |
| Browser DOM events | partial | `src/lib/gc_async_mut/gpu/browser_engine/dom.spl`; `src/lib/gc_async_mut/gpu/browser_engine/layout.spl`; `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl`; `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl` | Simplified `BeDomNode` listener registration, event-name normalization, inline `on...` handler discovery, lightweight Event state (`type`, `target`, `currentTarget`, `bubbles`, `cancelable`, `defaultPrevented`, propagation stop flags), deterministic capture/target/bubble ordering, first-match tree path discovery by target id, layout-box coordinate hit-test routing to root-to-target pointer/click dispatch, deterministic mousedown/up sequencing with click synthesis only when both phases hit the same target, focused default-action metadata, cancelable default suppression, simplified returned-node default effects for checkbox/radio/focus/button/form/navigation tokens, disabled control default suppression, focused Enter/Space keyboard activation mapping to click/default effects for common interactive elements, and deterministic `stop-propagation` / `stop-immediate-propagation` listener-token behavior are covered. Executable JavaScript listener callbacks, composed paths, shadow DOM retargeting, real PointerEvent/MouseEvent payload fields, pointer capture, full keyboard event dispatch, async event-loop delivery, and document-wide default-action side effects remain unsupported. |

## Verification

Required focused commands after DOM event work:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/dom.spl test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl --mode=interpreter --clean`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl --mode=interpreter --clean`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --mode=interpreter --clean`
- `bin/simple check src/lib`
