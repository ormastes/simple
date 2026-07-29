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
- The compositor/hosted registry own four keyed external renderer/frame slots;
  missing frames stay blank, hidden windows poll cleanup without animation.
- Navigation/close clears document references; warnings are deduplicated and
  bounded; diagnostics are prefix-only and failed child cleanup is retried.
- Wheel deltas coalesce in one bounded renderer slot; the sandbox worker owns
  clamped scroll, shifted Draw IR/hit testing, and viewport culling.
- Broker owns URLs/origins, Fetch/CORS/CSP, cookies, TLS/HSTS, and host access.
- Static `<img>` and CSS URL backgrounds share bounded broker image policy;
  retained `SBRF5` frames include only composition-referenced resources.
  Rounded background shape/radius metadata is masked during the sampling pass,
  with aggregate CSS-background work capped at one framebuffer per composition.
- Post-load JS/Simple Script backgrounds reuse `_start_image_source`; Stop is
  deferred across partial IPC, buffered messages drain in place, IPv6 TLS gets
  a validated bare host, and final seccomp denies `get_robust_list`.
- Zero-opacity subtrees are skipped; fractional subtree opacity awaits bounded
  group compositing. One bookmark snapshot/revision feeds primary, secondary,
  and new windows; Escape restores committed-or-startup URL in both lanes.
- Deferred resizes coalesce and each animation frame serializes HTML once.
- Linux/macOS/Windows sandbox failure blocks production startup.

Hot-path evidence: stage counters/timings, frame/input latency, cache reuse,
Engine2D/font create/shutdown counts, memtrack/heap/RSS, 10,000-cycle soak.
Current executable evidence is host C only; pure-Simple runtime evidence remains
compiler-blocked and no bootstrap/seed substitute is accepted.

Next files:

- `doc/05_design/simple_web_browser_engine_production_hardening.md`
- `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- `doc/03_plan/agent_tasks/simple_web_browser_engine_production_hardening.md`
