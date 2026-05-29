# ECMAScript Feature Matrix

Date: 2026-05-06

Scope: JavaScript compatibility planning for the Simple browser goal. Status values are `supported`, `partial`, `missing`, and `not-applicable`.

## Host Integration

| Feature | Status | Evidence | Notes |
| --- | --- | --- | --- |
| DOM event integration | partial | `src/lib/gc_async_mut/gpu/browser_engine/dom.spl`; `src/lib/gc_async_mut/gpu/browser_engine/layout.spl`; `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl`; `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl` | Browser renderer DOM nodes now support focused listener registration, inline handler dispatch evidence, lightweight Event object state, deterministic capture/target/bubble propagation, target-id tree path discovery, layout-box coordinate hit-test routing to pointer/click dispatch, mousedown/up sequencing with click synthesis only when both phases hit the same target, default-action metadata including suppression through `prevent-default` listener tokens on cancelable events, simplified returned-node default effects for common controls/navigation tokens, disabled control default suppression, focused Enter/Space activation mapping to click/default effects for common interactive elements, and propagation control through deterministic stop listener tokens. Full Web Events semantics, executable JavaScript listener callbacks, composed/shadow path semantics, document-wide default-action side effects, real PointerEvent/MouseEvent payloads, pointer capture, full keyboard event dispatch, and JavaScript event-loop integration remain incomplete. |
| History, storage, broad Web APIs | missing | `doc/03_plan/chrome_modern_web_platform_compat_plan.md` | Track as unsupported-host until implemented and tested. |

## Verification

Required focused commands after DOM event host-integration work:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/dom.spl test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl --mode=interpreter --clean`
- `bin/simple test test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl --mode=interpreter --clean`
- `bin/simple check src/lib`
