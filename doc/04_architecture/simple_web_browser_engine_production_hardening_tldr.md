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
- Proposed DOM identity uses one immutable two-pass index per generation.
  Import-free `dom_limits.spl` owns only tree depth/node count; layout hits
  become `DomNodeRoute` through a generation-gated session lookup. Body-rooted
  paths use `(parent route, layout-element-child ordinal)` and ignore
  interspersed text/non-layout nodes.
- Event routing, hosted press/focus, UI access, callable listeners,
  SimpleScript, and JavaScript carry typed routes. Script DOM, index, bridge,
  runtime state, runner roots, listeners, and callbacks publish atomically,
  including load-time binding; staging failure rolls all of them back and
  stale generations never retry in the new index.
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

The DOM identity migration is one-tree only. It removes recursive identity
lookup, NUL/bare route parsing, text dispatch route fields, and hosted bare
press/focus IDs only when index, accessors/forms, dispatch/scripts, and
UI/hosted hit conversion compile together. General DOM layout/serialization
walks, renderer/resource/Draw IR node IDs, JS heap IDs, and page-visible
author-ID projections remain non-routing data; a missing author ID never
projects `node:<node_id>`, and production author lookup uses the O(1) index.
Retirement clears are staged into the same publication boundary. Its
ownership/API audit is resolved; implementation and execution remain RED.

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

The private parent creator reuses only
`crypto_sffi.random_hex(16)` and the common
`browser_renderer_command_capability_valid`, rejecting the result before any
mutation.
Security comes from the parent-only issued tuple, full-wire disclosure, exact
generation/root/immediate-wire correlation, and one-use retirement—not from
preventing trusted code from formatting bytes. The common codec validates and
frames; codec and worker do not own or import the private creator and cannot
install or consume parent `issued_*`; the worker only echoes a complete-wire
trailer. Common codec, parent, worker, every command/network/fetch/frame
direction, and cleanup migrate atomically, with no downgrade flag or mixed
SBR1/SBR2 state.

Next files:

- `doc/05_design/simple_web_browser_engine_production_hardening.md`
- `doc/03_plan/sys_test/simple_web_browser_engine_production_hardening.md`
- `doc/03_plan/agent_tasks/simple_web_browser_engine_production_hardening.md`
