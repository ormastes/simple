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
- BrowserSession reuses its repaired UI-access revision as the document
  revision and adds only style/resource revisions; the renderer owns viewport
  and composition revisions. One retained private stage set lowers directly
  to Draw IR—no Web IR or second pixel cache.
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
  Exactly two URL background-image layers reuse this chain and emit back then
  front typed Draw-IR commands; broader layer syntax remains unsupported.
  Rounded background shape/radius metadata is masked during the sampling pass,
  with aggregate CSS-background work capped at one framebuffer per composition.
- Post-load JS/Simple Script backgrounds reuse `_start_image_source`; Stop is
  deferred across partial IPC, buffered messages drain in place, IPv6 TLS gets
  a validated bare host, and final seccomp denies `get_robust_list`.
- Zero-opacity subtrees are skipped; fractional subtree opacity awaits bounded
  group compositing. One bookmark snapshot/revision feeds primary, secondary,
  and new windows; Escape restores committed-or-startup URL in both lanes.
- Deferred resizes coalesce. Unchanged frames serialize nothing; scroll/caret
  reuse raw layout, and CSS animation frames reuse parse/CSS/base style.
- Visible material hashes collect ordered lines and join once, avoiding
  quadratic transient text without changing animation or Draw-IR output.
- Linux/macOS/Windows sandbox failure blocks production startup.

Hot-path evidence: stage counters/timings, frame/input latency, cache reuse,
Engine2D/font create/shutdown counts, memtrack/heap/RSS, 10,000-cycle soak.
Current executable evidence is host C only; pure-Simple runtime evidence remains
compiler-blocked and no bootstrap/seed substitute is accepted.

Proposed `SBRF8` binds a 512-byte document-title witness to generation, reply,
and committed URL. Invalid or missing titles derive the canonical URL only at
display time, never by copying it into bounded title storage. Its canonical
base64 length is prebounded to 684 and charged, encoded plus decoded, to the
existing 1 MiB frame budget before allocation.

Proposed `SBR2` adds a fresh host-generated 128-bit tail capability to every
host-to-worker wire, including each network response. The next worker
fetch/frame may consume it once and must match generation, stable root request
ID, opaque capability, and immediate reply ID before broker or frame state
changes. Network responses also name their originating fetch wire. Platform
entropy failure and all legacy numeric-only production schemas fail closed;
`ready` must leave no buffered bytes. Status remains UNIMPLEMENTED/RED.

Pending wires stage authority; only a complete write atomically promotes the
tuple to issued authority. The 32-byte trailer is charged inside the existing
1 MiB payload and total streaming-buffer caps. Stop/cancel retires authority
but keeps the last frame; fail/close/site swap clears authority and images.
Warm capability generation p95 is <=1 ms, total input-to-paint remains <=50 ms,
and 10,000-cycle RSS growth remains <=10% after quiescence.

Token creation is native-only and private to
`hosted_browser_renderer_process.spl`. One fatal compiler policy binds its raw
import to that canonical physical source path; interpreters and dynamic SFFI
have no handler, and the raw ABI binds only through the admitted runtime
provider. Existing hosted-entry source/runtime receipts bind the owner, policy,
closure, runtime, and artifact digests. Codec, entropy, parent, worker, and
cleanup migrate atomically—no public entropy facade or mixed SBR1/SBR2 state.

Next files:

- `doc/05_design/simple_web_browser_engine_production_hardening.md`
- `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- `doc/03_plan/agent_tasks/simple_web_browser_engine_production_hardening.md`
