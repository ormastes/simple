# Simple Browser — Chrome-Class Roadmap

**Date:** 2026-05-07
**Baseline:** V3 M1–M12 landed (2026-04-14), 132/132 pixel-parity corpus, Acid2 pass, 30/30 design effects

---

## 1. Gap Analysis — Current State vs Chrome

### 1.1 Rendering & CSS

| Category | Chrome | Simple (V3) | Gap |
|----------|--------|-------------|-----|
| CSS spec coverage | ~98% | Widget-subset only | WPT 37.8% (15/50) |
| Float layout | Full | None | 0% WPT, blocks 32% of tests |
| Flexbox | Full | Partial | 55.6% WPT (10/18) |
| Grid | Full | Partial | Exists in examples tree, not wired |
| Colors (hsl, currentColor) | Full | Partial | 30% WPT (3/10) |
| Display modes | Full | block/inline/flex only | 0% WPT (0/5); no contents, flow-root |
| Backgrounds | Full | Partial | 20% WPT (1/5) |
| Positioning | Full | Partial | 20% WPT (1/5) |
| Normal flow | Full | Partial | 0% WPT (0/2) |
| Text shaping | HarfBuzz/ICU | Basic | No bidi, no complex scripts |
| Animations/transitions | Full | None | No @keyframes, transition, requestAnimationFrame |
| Media queries | Full | Basic | Viewport only, no prefers-* |

### 1.2 JavaScript

| Feature | Chrome (V8) | Simple | Gap |
|---------|-------------|--------|-----|
| Engine | V8, JIT, IC, OSR | 8,220-line engine in examples/browser/feature/script/ | Lexer+parser+bytecode+VM+JIT+GC exist but NOT wired to V3 |
| ES spec compliance | ~100% ES2024 | Unknown subset | No Test262 harness run |
| DOM bindings | Full Web IDL | 7 web API stubs (console, crypto, dom, event, fetch, timer, worker) | Stubs only, not production |
| Event loop | Spec-compliant | None in V3 | M6 was deferred from V3 |
| Async | Promises, async/await, generators | Promise builtin exists | Not wired |

### 1.3 Networking

| Feature | Chrome | Simple | Gap |
|---------|--------|--------|-----|
| HTTP/1.1 | Full | h1_client.spl in examples tree | Not wired to V3 |
| HTTP/2 | Full (HPACK, streams) | h2_client.spl exists | Not wired |
| HTTP/3 / QUIC | Full | None | Missing entirely |
| TLS 1.3 | BoringSSL | tls.spl exists | Not wired, maturity unknown |
| DNS | Full (DoH, DoT) | dns.spl exists | Not wired |
| WebSocket | Full | websocket_client.spl exists | Not wired |
| Fetch API | Full | fetch.spl exists | Not wired |
| Service Workers | Full | None | Missing entirely |
| Cache API | Full | cache.spl exists | Not wired |
| Cookies | Full | cookie_store.spl exists | Not wired |
| CORS | Full | cors.spl exists | Not wired |

### 1.4 Security & Process Model

| Feature | Chrome | Simple | Gap |
|---------|--------|--------|-----|
| Multi-process | Renderer/GPU/browser/utility | Single-process | sandbox/ tree exists (4 files) but not used |
| Site isolation | Full | None | site_isolation.spl exists, not wired |
| Sandboxing | seccomp-bpf / Seatbelt | None | capability_broker.spl exists, not wired |
| CSP | Full | csp.spl exists | Not wired |
| Same-origin policy | Full | None | Missing |
| Mixed content blocking | Full | None | Missing |
| Certificate validation | Full | None | Missing |

### 1.5 Web Platform APIs

| API | Chrome | Simple | Gap |
|-----|--------|--------|-----|
| Canvas 2D | Full | None | Missing |
| WebGL / WebGPU | Full | None | Missing (GPU tree exists for compositing) |
| localStorage/sessionStorage | Full | None | Missing |
| IndexedDB | Full | None | Missing |
| Web Audio | Full | None | Missing |
| Video/Audio elements | Full | None | Missing |
| Web Workers | Full | worker binding stub | Missing |
| WebRTC | Full | None | Missing |
| Geolocation | Full | None | Missing |
| Notifications | Full | None | Missing |
| Clipboard | Full | None | Missing |
| Drag & Drop | Full | None | Missing |
| History API | Full | history.spl in browser/ | Partial |
| Intersection/Mutation/Resize Observer | Full | mutation_observer.spl exists | Partial |

### 1.6 Developer Tools

| Feature | Chrome | Simple | Gap |
|---------|--------|--------|-----|
| DevTools Protocol (CDP) | Full | None | devtools.spl exists in browser/, not a protocol server |
| Elements panel | Full | None | Missing |
| Console | Full | None | Missing |
| Network panel | Full | None | Missing |
| Performance profiler | Full | None | Missing |
| JS debugger | Full | None | Missing |

### 1.7 Pixel Compatibility

- **Corpus:** 132/132 exact match
- **Semrush top-20:** 14/20 covered (all 14 exact)
- **Missing sites:** DuckDuckGo, Yahoo Japan, Microsoft Online, Pornhub, XVideos, XHamster

---

## 2. Architecture Decisions

### AD-1: Engine Unification Strategy

**Decision:** Migrate examples/browser features INTO the canonical engine (`src/lib/gc_async_mut/gpu/browser_engine/`) incrementally, subsystem by subsystem.

**Rationale:** ADR-002 established the canonical engine as production. The examples tree (~62k lines) contains mature subsystems (parser, layout, paint, composite, script, net, sandbox) that are individually portable. Each milestone below moves one subsystem from examples → canonical, validates via WPT/corpus gates, then deletes the examples copy.

**Approach:**
1. Each subsystem moves as a unit (all files in a feature/ directory)
2. Adapter layer in canonical engine wraps the moved subsystem
3. Old examples/ path becomes a re-export shim during transition, then deleted
4. ChromiumEngine in `engine_merge.spl` grows new pipeline stages as subsystems land

### AD-2: JavaScript Engine Approach

**Decision:** Wire the existing Simple-native JS engine (`examples/browser/feature/script/`, 8,220 lines) into V3 via ChromiumEngine.

**Rationale:** The engine already has lexer, parser, bytecode compiler, VM, GC, and 7 web API binding stubs. Building on this avoids external dependencies and aligns with the project's "all code in .spl" rule. JIT compilation exists but should remain disabled until correctness is proven via Test262.

**Approach:**
1. Move script/ tree into canonical engine namespace
2. Create `JsRuntime` class in canonical engine that owns VM + GC lifecycle
3. Wire DOM bindings: `document.getElementById` etc. map to BeDomNode queries
4. Implement event loop as a message queue in ChromiumEngine's frame scheduler
5. Gate: Test262 pass rate as quantitative measure (target: 70% core by M15)

### AD-3: Multi-Process Model

**Decision:** Phased adoption — start with thread-isolated renderer, then process-separated.

**Rationale:** Full process isolation (Chrome's model) requires IPC, shared-memory GPU command buffers, and a process manager. The existing `process_manager.spl` and `site_isolation.spl` provide a starting framework. Going directly to multi-process before networking and JS work is premature.

**Approach:**
1. **Phase 1 (M19):** Thread-isolated renderer — renderer runs in dedicated thread, browser chrome in main thread, message-passing between them
2. **Phase 2 (M22):** Process-separated renderer — renderer in child process, Mojo-style IPC
3. **Phase 3 (M24):** Site isolation — one renderer process per site, capability-brokered sandbox

### AD-4: Networking Stack

**Decision:** Wire the existing examples/browser/feature/net/ stack, then harden.

**Rationale:** The net stack (DNS, TLS, HTTP/1, HTTP/2, WebSocket, fetch, cache, cookies, CORS) exists as 9 files. Integration before rewrite — get real pages loading, then fix issues discovered by real-world traffic. Known risk: text-typed APIs corrupt binary data (memory: `feedback_text_only_byte_cliffs.md`), requiring a `[u8]` byte-buffer path.

---

## 3. Milestone Roadmap (M13–M24)

### Priority Tiers (by real-world site impact)

**Tier 1 — Unlocks the most sites:**
1. Float layout (32% of WPT tests depend on it; nearly all real sites use floats)
2. CSS quick wins: hsl(), currentColor, display:contents/flow-root, list-style:none
3. JS engine wired to V3 (modern web is JS-dependent; without JS, most sites show blank)
4. Real networking (without HTTP, browser can only render local HTML strings)

**Tier 2 — Major feature categories:**
5. Full CSS3 coverage (animations, transforms, transitions, media queries)
6. Canvas 2D / WebGL (required by many interactive sites, maps, charts)
7. Web platform APIs (localStorage, fetch from JS, history)
8. Text shaping (bidi, complex scripts — required for non-Latin sites)

**Tier 3 — Production hardening:**
9. Multi-process / sandboxing
10. DevTools protocol
11. Service Workers / PWA
12. Media (video/audio)

---

### M13 — Float Layout & CSS Quick Wins

**Goal:** Raise WPT from 37.8% to 65%+ by landing float layout and low-effort CSS gaps.

**Work:**
- Port `examples/browser/feature/layout/float.spl` → canonical engine
- Implement float clearing, float context, float positioning per CSS 2.1 spec
- Land CSS quick wins: `hsl()`/`hsla()`, `currentColor`, `display: inline-flex`, `display: flow-root`, `display: contents`, `list-style: none`, `flex-flow` shorthand
- Add `calc()` for length values

**Gate:** WPT pass rate >= 65% (currently 37.8%). Float category >= 80%. All 132 corpus pages still exact match.

---

### M14 — HTML Parser Upgrade & Normal Flow

**Goal:** WHATWG-compliant HTML parser in canonical engine; normal flow layout complete.

**Work:**
- Port `examples/browser/feature/parser/html_tokenizer.spl` + tree builder (5 state files) → canonical engine, replacing the current minimal parser
- Implement missing insertion modes: in_head, in_select, in_template, after_after_body, foreign_content
- Complete normal flow: margin collapse, inline formatting context, anonymous block generation
- Add `<table>` layout (basic — rows, cells, auto column sizing)

**Gate:** WHATWG tokenizer test suite >= 90% pass. Normal flow WPT 100% (2/2 → 2/2). Table rendering for Wikipedia-class pages. 132 corpus still green.

---

### M15 — JavaScript Engine Integration

**Goal:** JS executes in V3 shell. DOM manipulation works. Event loop runs.

**Work:**
- Move `examples/browser/feature/script/` → `src/lib/gc_async_mut/gpu/browser_engine/script/`
- Create `JsRuntime` class: owns VM lifecycle, GC, bytecode store
- Wire DOM bindings: `document.getElementById`, `document.querySelector`, `element.textContent`, `element.style`, `element.classList`, `element.addEventListener`
- Implement event loop: microtask queue (Promise resolution), macrotask queue (setTimeout, setInterval), requestAnimationFrame
- Wire `console.log` → browser DevTools console buffer

**Gate:** Test262 core language >= 70% pass (excluding Annex B). `setTimeout` + `addEventListener('click')` + DOM mutation work in a test page. DuckDuckGo search page renders with JS (adds it to top-20 coverage: 15/20).

---

### M16 — Networking Stack

**Goal:** Browser loads pages from the internet via HTTP/1.1 and HTTP/2.

**Work:**
- Move `examples/browser/feature/net/` → canonical engine
- Wire `fetch()` API in JS runtime to net stack
- Implement resource loader: HTML, CSS, images, JS — with Content-Type dispatch
- Add `[u8]` byte-buffer path to fix text-typed API corruption (R2 risk)
- Implement same-origin policy for fetches
- Cookie storage wired to HTTP requests (cookie_store.spl)
- TLS certificate validation (trust system CA bundle)
- Navigation: URL bar → DNS → TLS → HTTP → parse → render pipeline

**Gate:** Browser loads and renders google.com homepage. HTTP/1.1 and HTTP/2 both work. CORS enforcement passes basic WPT CORS tests. Yahoo Japan renders (adds to top-20: 16/20).

---

### M17 — CSS3 Completeness (Animations, Transforms, Transitions)

**Goal:** Raise WPT to 80%+. Visual effects match Chrome for CSS3 sites.

**Work:**
- CSS Transitions: `transition` property, interpolation engine for color/length/transform values
- CSS Animations: `@keyframes`, `animation` shorthand, timing functions (ease, cubic-bezier)
- CSS Transforms: `transform` property (translate, rotate, scale, skew, matrix), `transform-origin`
- CSS `position: sticky`
- CSS `overflow: auto/scroll` with scrollbar rendering
- CSS `object-fit` / `object-position` for images
- CSS custom properties (`--var`) full spec (currently partial)
- CSS `@supports` rule

**Gate:** WPT overall >= 80%. Animations render on CSS-animated landing pages (test: animate.style demo). All 132 corpus still green. Microsoft Online loads with layout intact (17/20 top sites).

---

### M18 — Advanced Selectors & Text Shaping

**Goal:** Full CSS selector support. Non-Latin text renders correctly.

**Work:**
- Selectors: `:nth-child(An+B)`, `:not()`, `:is()`, `:where()`, `:has()`, `::before`/`::after` with `content`, attribute selectors `[attr^=val]`/`[attr$=val]`/`[attr*=val]`
- CSS `@font-face` with font loading from network
- Text shaping: integrate or implement bidi algorithm (UAX #9), complex script shaping (Arabic joining, Devanagari conjuncts)
- Line breaking: UAX #14 (line break), UAX #29 (grapheme cluster)
- `text-overflow: ellipsis`, `word-break`, `overflow-wrap`

**Gate:** Selector WPT >= 95%. Arabic Wikipedia article renders correctly (RTL layout, joined glyphs). CJK text wraps correctly. All corpus green.

---

### M19 — Thread-Isolated Renderer & Canvas 2D

**Goal:** Renderer runs in dedicated thread. Canvas 2D API available to JS.

**Work:**
- Split ChromiumEngine into browser thread (chrome, navigation, tabs) + renderer thread (DOM, layout, paint, composite)
- Message-passing bridge between threads (post-message style)
- Canvas 2D API: `getContext('2d')`, path operations (moveTo, lineTo, arc, bezierCurveTo), fill/stroke, drawImage, text rendering, pixel manipulation (getImageData/putImageData)
- `<canvas>` element in DOM
- Wire canvas to GPU raster pipeline

**Gate:** Canvas 2D passes canvas2d WPT basic tests. Thread isolation: renderer crash doesn't kill browser chrome (inject fault, verify recovery). Chart.js demo renders.

---

### M20 — Web Platform APIs

**Goal:** Core web APIs available to JS.

**Work:**
- `localStorage` / `sessionStorage` (backed by per-origin file storage)
- `history.pushState` / `popstate` event (SPA navigation)
- `XMLHttpRequest` (legacy compat, delegates to fetch internally)
- `FormData`, `URLSearchParams`, `URL` classes
- `IntersectionObserver`, `ResizeObserver` (wire existing mutation_observer.spl patterns)
- `Clipboard` API (read/write text)
- `navigator` object (userAgent, language, onLine, etc.)
- `window.location`, `window.open`, `window.close`

**Gate:** A React SPA (e.g., TodoMVC React) loads and navigates without full-page reloads. localStorage persists across sessions. Pornhub renders (JS-heavy, 18/20). XVideos renders (18/20 or 19/20).

---

### M21 — Full CSS Grid & Advanced Layout

**Goal:** CSS Grid Layout fully functional. Remaining layout edge cases resolved.

**Work:**
- Port and complete `examples/browser/feature/layout/grid.spl`
- Grid: explicit/implicit tracks, `fr` unit, `minmax()`, `repeat()`, auto-fill/auto-fit, named lines, grid areas, alignment (justify/align-items/content/self)
- Multi-column layout (port multicol.spl)
- CSS `writing-mode` (vertical text)
- CSS `contain` / `content-visibility` (rendering performance)
- Subgrid

**Gate:** CSS Grid WPT >= 90%. Multi-column article renders. Vertical CJK text works. XHamster renders (JS + grid-heavy, 20/20 top sites).

---

### M22 — Process Isolation & Security Hardening

**Goal:** Renderer in separate process. Security sandbox active.

**Work:**
- Process-separate renderer via child process spawn + IPC (Mojo-style message passing)
- Port `examples/browser/feature/sandbox/` → canonical engine
- Capability broker: renderer has no direct filesystem/network access
- CSP enforcement (Content-Security-Policy header parsing + policy evaluation)
- Mixed content blocking (HTTPS page blocking HTTP subresources)
- `Referrer-Policy` enforcement
- Subresource Integrity (SRI) for `<script>` and `<link>`

**Gate:** Renderer runs in separate process (verify via process list). Injected renderer crash doesn't affect browser chrome or other tabs. CSP `script-src` blocks inline scripts correctly. Mixed content blocked by default.

---

### M23 — DevTools Protocol

**Goal:** Chrome DevTools Frontend connects to Simple Browser via CDP.

**Work:**
- Implement Chrome DevTools Protocol (CDP) WebSocket server
- Domains: `Runtime` (evaluate, console), `DOM` (getDocument, querySelector, getAttributes), `CSS` (getComputedStyle, getMatchedStyles), `Network` (requestWillBeSent, responseReceived, loadingFinished), `Page` (navigate, reload, screenshot)
- Elements panel: live DOM tree, computed styles, box model overlay
- Console panel: JS evaluate, console.log output
- Network panel: request waterfall, headers, response body
- Wire to existing devtools.spl browser chrome UI as local alternative

**Gate:** Chrome DevTools Frontend (standalone) connects to Simple Browser on localhost:9222. Can inspect DOM, evaluate JS in console, see network requests. Page.screenshot returns valid PNG.

---

### M24 — Media, Service Workers & PWA

**Goal:** Video/audio playback. Offline-capable PWAs.

**Work:**
- `<video>` / `<audio>` elements with HTMLMediaElement API
- Media decoder integration (codec support: H.264/VP9/AV1 via FFmpeg or native decoders)
- Media controls UI (play/pause, seek, volume, fullscreen)
- `MediaSource` API (adaptive streaming)
- Service Worker lifecycle (register, install, activate, fetch intercept)
- Cache API (for Service Worker offline storage)
- Web App Manifest (`manifest.json` parsing, install prompt)
- Push API / Notifications

**Gate:** YouTube embedded video plays (or a self-hosted MP4 test). Service Worker intercepts fetch and serves cached response offline. PWA installs to desktop with icon.

---

## 4. Priority Ranking by Real-World Site Impact

Sites are ranked by Semrush global traffic. Each milestone's gate criterion includes specific sites it unlocks.

| Rank | Site | Primary Blocker | Unlocked At |
|------|------|-----------------|-------------|
| 1 | Google | JS + Networking | M16 |
| 2 | YouTube | JS + Media | M24 |
| 3 | Facebook | JS + Networking + CSS3 | M17 |
| 4 | Instagram | JS + CSS Grid | M21 |
| 5 | Twitter/X | JS + CSS3 + SPA | M20 |
| 6 | Wikipedia | HTML tables + Normal flow | M14 |
| 7 | Reddit | JS + CSS Grid + SPA | M21 |
| 8 | Amazon | JS + Networking + Floats | M16 |
| 9 | DuckDuckGo | JS | M15 |
| 10 | Yahoo Japan | Networking + CJK text | M18 |
| 11 | Microsoft Online | CSS3 + JS | M17 |
| 12 | LinkedIn | JS + CSS3 + SPA | M20 |
| 13 | Pornhub | JS + Web APIs | M20 |
| 14 | XVideos | JS + Web APIs | M20 |
| 15 | XHamster | JS + CSS Grid | M21 |

**Cumulative top-20 coverage by milestone:**

| Milestone | Top-20 Coverage | Cumulative Sites |
|-----------|----------------|-----------------|
| M12 (current) | 14/20 (70%) | 14 existing corpus matches |
| M15 | 15/20 (75%) | +DuckDuckGo |
| M16 | 16/20 (80%) | +Yahoo Japan |
| M17 | 17/20 (85%) | +Microsoft Online |
| M20 | 19/20 (95%) | +Pornhub, XVideos |
| M21 | 20/20 (100%) | +XHamster |

---

## 5. Risk Register

### R1: Interpreter-Mode False Greens
**Impact:** High — tests pass in interpreter but fail compiled.
**Mitigation:** All gate criteria must pass in compiled mode (`--mode=native`). Until R2-broader lands, also verify in interpreter mode and cross-check.
**Ref:** `feedback_compile_mode_false_greens.md`

### R2: Text-Typed API Byte Corruption
**Impact:** High — networking stack (`fetch`, HTTP bodies, TLS) will corrupt binary data if using `text` (String) types.
**Mitigation:** M16 must introduce `[u8]` byte-buffer path before wiring net stack. File feature request for `Bytes` type if not available.
**Ref:** `feedback_text_only_byte_cliffs.md`

### R3: Parser Strictness at Callsites
**Impact:** Medium — interpreter rejects named-arg calls, `me`-receiver, and `{struct.field}` interpolation that lint accepts.
**Mitigation:** Use positional args, `self`, and temp-var workarounds. Track compiler bug fixes; remove workarounds when fixed.
**Ref:** `feedback_simple_parser_strict_callsites.md`

### R4: Bootstrap Rebuild for New Externs
**Impact:** Medium — each new `rt_*` extern requires `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`.
**Mitigation:** Batch extern additions within milestones. Run bootstrap rebuild at milestone boundaries, not per-commit.
**Ref:** `feedback_extern_bootstrap_rebuild.md`

### R5: Engine Unification Breakage
**Impact:** Medium — moving subsystems from examples/ → canonical may break existing V3 imports or ChromiumEngine pipeline.
**Mitigation:** Each move is one subsystem at a time with adapter layer. 132-corpus regression test after every move. Rollback if corpus breaks.

### R6: JS Engine Maturity Unknown
**Impact:** High — 8.2k-line JS engine has never run Test262. JIT is untested. GC may have issues under load.
**Mitigation:** M15 gate requires Test262 >= 70% core. Disable JIT initially (interpreter-only). Add GC stress tests.

### R7: TLS/Networking Maturity
**Impact:** High — net stack exists but has never been used against real servers. TLS handshake, certificate chains, ALPN negotiation all untested.
**Mitigation:** M16 should start with HTTP-only (no TLS) against local test server, then add TLS incrementally. Use known-good test endpoints.

### R8: Multi-Process IPC Performance
**Impact:** Medium — Simple language may not have efficient IPC primitives (shared memory, zero-copy message passing).
**Mitigation:** Deferred to M19/M22. Design IPC protocol during M19 (thread-isolated) before committing to process separation in M22. Profile message throughput.

### R9: Memory Pressure from Parallel Subsystems
**Impact:** Medium — running JS engine + layout engine + compositor + network stack in same process may exceed memory budgets.
**Mitigation:** Profile RSS at each milestone. M19 thread isolation helps. M22 process isolation is the ultimate fix.

### R10: Font/Text Shaping Complexity
**Impact:** Low-Medium — complex scripts (Arabic, Devanagari, Thai) require state machines and lookup tables that are large and subtle.
**Mitigation:** M18 can start with Latin + CJK (covers 80%+ of web traffic). Complex scripts can be a follow-up (M25+).

---

## 6. Subsystem Migration Schedule

Each subsystem migrates from `examples/browser/feature/` → `src/lib/gc_async_mut/gpu/browser_engine/` per AD-1.

| Subsystem | Source | Lines | Target Milestone | Dependencies |
|-----------|--------|-------|-----------------|--------------|
| layout/float | examples/browser/feature/layout/float.spl | ~500 | M13 | None |
| parser/html_* | examples/browser/feature/parser/ | ~2,000 | M14 | None |
| script/* | examples/browser/feature/script/ | 8,220 | M15 | M14 (DOM for bindings) |
| net/* | examples/browser/feature/net/ | ~1,500 | M16 | M15 (fetch API binding) |
| style/cascade | examples/browser/feature/style/ | ~1,000 | M17 | M14 (parser) |
| layout/grid | examples/browser/feature/layout/grid.spl | ~800 | M21 | M17 (style) |
| composite/* | examples/browser/feature/composite/ | ~1,000 | M19 | M17 (animations) |
| gpu/* | examples/browser/feature/gpu/ | ~1,000 | M19 | composite |
| sandbox/* | examples/browser/feature/sandbox/ | ~600 | M22 | M19 (threads) |
| browser/devtools | examples/browser/feature/browser/devtools.spl | ~300 | M23 | M15 (JS runtime) |

---

## 7. WPT Progress Targets

| Milestone | Target WPT % | Key Categories Unlocked |
|-----------|-------------|------------------------|
| M12 (now) | 37.8% | Partial flex, partial colors |
| M13 | 65% | Floats, hsl, currentColor, display modes |
| M14 | 70% | Normal flow, tables |
| M17 | 80% | Animations, transforms, transitions |
| M18 | 85% | Advanced selectors, text |
| M21 | 90% | Grid, multi-column |
| M24 | 92%+ | Media, remaining edge cases |

---

## 8. Summary Timeline

```
M13  Float + CSS Quick Wins         ← highest WPT impact
M14  HTML Parser + Normal Flow      ← WHATWG compliance
M15  JS Engine Integration          ← enables modern web
M16  Networking Stack               ← loads real pages
M17  CSS3 Completeness              ← visual parity
M18  Selectors + Text Shaping       ← i18n, non-Latin
M19  Thread Isolation + Canvas 2D   ← performance, interactivity
M20  Web Platform APIs              ← SPA support
M21  CSS Grid + Advanced Layout     ← remaining layout
M22  Process Isolation + Security   ← production hardening
M23  DevTools Protocol              ← developer experience
M24  Media + Service Workers + PWA  ← full platform
```

Ordering rationale: Each milestone builds on the previous. Floats and CSS quick wins (M13) are first because they have the highest WPT-per-effort ratio. JS (M15) before networking (M16) because the fetch API binding needs JS runtime. Networking before CSS3 (M17) because CSS3 animations are less impactful than loading real pages. Security hardening (M22) after the core feature set is complete because sandboxing a broken renderer is premature optimization.
