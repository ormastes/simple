<!-- codex-research -->
# Simple Web Browser Engine Production Hardening — Local Research

Date: 2026-07-26

## Canonical owners

- ADR-002 selects `src/lib/gc_async_mut/gpu/browser_engine/`; the large
  `examples/11_advanced/browser/**` tree is research only.
- `src/lib/gc_async_mut/web/BrowserSession` owns page/runtime/navigation state.
- Production pixels currently route through `BrowserRenderer` and the
  `simple_web_html_layout_renderer*` stages to canonical `DrawIrComposition`.
- `src/lib/gc_async_mut/gpu/engine2d/` owns device, text, font, and transient
  raster material.

## Confirmed gaps

- Production paint uses a heuristic HTML path alongside the canonical
  tokenizer/tree builder; no third parser should be added.
- Full CSS status is incomplete (262/394 inventory rows in the retained
  report); animation evidence does not prove changing production frames.
- BrowserSession timers drain at time zero and have no rAF rendering loop.
- DOM mutation/event helpers are disconnected or target-only.
- Address advertises `set_value` but the action handler rejects non-click
  actions.
- BrowserSession directly reads `file://` host paths.
- Page runtimes expose `require`, `process`, and `Buffer`.
- Cookies omit host-only, Secure, HttpOnly, and SameSite enforcement.
- Browser HTTPS types exist, but live production BrowserSession Fetch/TLS and
  bad-certificate evidence do not.
- Existing browser-interaction evidence passes when its artifact is missing.
- Each render reparses and can recreate Engine2D/read back the full frame.
- No browser-specific RSS, GC pause, 10,000-cycle soak, or retained-resource
  evidence exists.

## Existing evidence to reuse

- tokenizer/tree-builder, CSS cascade/vars, BrowserSession, JS, Draw IR, and
  Engine2D unit suites;
- HTML/CSS Chrome comparison corpus;
- BrowserSession UI-access control spec;
- generic platform TLS/sandbox tests.

These are supporting evidence, not production acceptance.

## Root direction

Reuse BrowserSession and the accepted browser/Draw IR/Engine2D owners. Add a
browser-only JS profile, canonical DOM/event path, persistent render session,
one clock, broker-owned URL/network/TLS/cookie policy, site renderer sandbox,
real lifecycle counters, and pinned conformance/fuzz evidence.

Parallel normal-model research was reviewed by root. Spark was unavailable.
