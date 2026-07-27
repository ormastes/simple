# Simple Web Browser Engine Production Hardening — TLDR

Purpose: selected B/B production browser with bounded compatibility, real
sandboxing, HTTPS, interaction, and measured GC/performance.

## Decision

```text
browser broker
  chrome/history + URL/origin + Fetch/TLS/cookies + sandbox
        |
        v
site-locked renderer
  BrowserSession + DOM/JS/events + SimpleWebRenderSession
        |
        v
DrawIrComposition -> persistent Engine2dCompositorBackend
```

- Reuse BrowserSession; add no chrome/history facade.
- Browser-only JS profile excludes Node/native capabilities.
- One canonical DOM event path and one monotonic animation/timer/rAF clock.
- One persistent render session with staged invalidation.
- Engine2D owns device/font/cache state; no per-frame recreation.
- Navigation/close clears document references; profile and engine lifetimes
  remain separate.
- Broker owns URLs/origins, Fetch/CORS/CSP, cookies, TLS/HSTS, and host access.
- Linux/macOS/Windows sandbox failure blocks production startup.

Hot-path evidence: stage counters/timings, frame/input latency, cache reuse,
Engine2D/font create/shutdown counts, memtrack/heap/RSS, 10,000-cycle soak.

Next files:

- `doc/05_design/simple_web_browser_engine_production_hardening.md`
- `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- `doc/03_plan/agent_tasks/simple_web_browser_engine_production_hardening.md`
