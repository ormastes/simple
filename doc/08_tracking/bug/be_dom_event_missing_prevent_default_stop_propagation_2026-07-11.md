---
id: be_dom_event_missing_prevent_default_stop_propagation_2026-07-11
status: OPEN
severity: low
discovered: 2026-07-11
discovered_by: event_api_spec (test/01_unit/browser/script/event_api_spec.spl)
related: src/lib/gc_async_mut/gpu/browser_engine/dom.spl
related: src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl
---

# BeDomEvent lacks prevent_default/stop_propagation methods and state

**Status:** OPEN. Gap lives in `dom.spl` (`BeDomEvent`), not owned by the
browser-script-API agent.

## Summary

`event_api.spl` exposes `event_prevent_default(event)` and
`event_stop_propagation(event)`, which call `event.prevent_default()` /
`event.stop_propagation()`. `BeDomEvent` (dom.spl) defines neither method, nor
any `default_prevented` / `propagation_stopped` field to record the state.

```
semantic: method `prevent_default` not found on type `BeDomEvent`
semantic: method `stop_propagation` not found on type `BeDomEvent`
```

Failing tests: `event_api_spec` "prevents default action", "stops propagation".

## Expected

`BeDomEvent` gains `default_prevented: bool` and `propagation_stopped: bool`
fields plus `me prevent_default()` / `me stop_propagation()` methods, so the
`event_api` forwarders can record and expose the flags.

## Resolution (2026-07-17)

FIXED (haiku fix lane F1, opus-reviewed APPROVE): BeDomEvent gained default_prevented/propagation_stopped bool fields + me prevent_default()/stop_propagation() (dom.spl). Behavioral repro via bootstrap seed prints default_prevented=true propagation_stopped=true, including through a forwarder-function call shape. Ctor at dom.spl:102 is the only construction site.
