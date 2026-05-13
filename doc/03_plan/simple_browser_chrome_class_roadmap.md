# Simple Browser — Chrome-Class Roadmap

**Date:** 2026-05-12
**Baseline:** V3 M1–M12 landed (2026-04-14), 132/132 pixel-parity corpus, Acid2 pass, 30/30 design effects. M18 pseudo-elements/text-overflow slice is complete, but the full Chrome-class browser program remains open.

## 0. Product Target

Build a Simple Browser that is production-ready for modern websites, not just a static HTML renderer.

Chrome-class means:
- Standards-first web engine: WHATWG HTML, modern CSS, ECMAScript, DOM, Fetch, Storage, Canvas, WebGL/WebGPU, media, workers, service workers, accessibility, and WebDriver/CDP-style automation.
- Real browser interface: tabs, omnibox, navigation controls, history, bookmarks, downloads, permissions, profile data, settings, page info/security indicators, password/autofill hooks, find-in-page, zoom, print, responsive/mobile emulation, and crash recovery.
- Modern graphics: GPU compositor, Canvas 2D, WebGL compatibility, WebGPU `navigator.gpu`, `canvas.getContext("webgpu")`, WGSL shader modules, render pipelines, compute pipelines, buffers/textures/samplers, feature/limit negotiation, validation, and GPU process isolation.
- Production criteria: secure-by-default networking, origin isolation, sandboxed renderer/GPU processes, deterministic conformance tests, top-site corpus rendering, memory/performance budgets, and no interpreter-only false greens.

Non-goal: cloning proprietary Chrome services. The target is Chrome-level web compatibility and user-facing browser quality using Simple-native implementation where feasible.

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
| 3D transforms/compositing | Full GPU compositor | Partial GPU tree | Needs layer tree, damage tracking, preserve-3d, perspective |

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
| WebGL | Full | None | Needed for compatibility with existing 3D sites |
| WebGPU | Modern GPU API | Backend guide exists, browser context not wired | Need secure-context API, WGSL validation, pipelines, compute, limits/features |
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

### 1.7 Browser Interface

| Feature | Chrome | Simple | Gap |
|---------|--------|--------|-----|
| Tabs/windows | Full | Minimal shell | Need tab model, session restore, crash recovery |
| Omnibox | Search + URL + suggestions | URL entry only | Need parse/search provider/history suggestions |
| History/bookmarks/downloads | Full | Not wired | Need persistent profile stores |
| Permissions/site settings | Full | None | Need prompts, per-origin decisions, revocation |
| Find/zoom/print | Full | None | Need browser chrome commands and page integration |
| Accessibility | Full platform tree | None | Need AX tree, focus navigation, ARIA mapping |

### 1.8 Pixel Compatibility

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

### AD-5: WebGPU and 3D Shading Strategy

**Decision:** Implement WebGPU as a first-class browser API and compositor backend, with WebGL compatibility layered separately for existing content.

**Rationale:** Current official WebGPU/WGSL references define WebGPU around adapter/device negotiation, `GPUCanvasContext`, render pipelines, compute pipelines, command encoders, and WGSL shader modules. MDN currently marks WebGPU as limited availability and secure-context only, so Simple Browser must expose it behind HTTPS/secure-origin rules, feature detection, validation, and compatibility fallback rather than treating it as always available.

**Approach:**
1. Wire `navigator.gpu`, `GPU.requestAdapter`, `GPUAdapter.requestDevice`, `GPUDevice`, `GPUQueue`, `GPUBuffer`, `GPUTexture`, `GPUSampler`, `GPUShaderModule`, `GPURenderPipeline`, `GPUComputePipeline`, `GPUCommandEncoder`, and `GPUCanvasContext`.
2. Use WGSL as the browser-facing shading language; validate shader modules before backend compilation.
3. Support core render and compute pipelines first: vertex/fragment/compute stages, bind groups, pipeline layouts, buffer/texture/sampler bindings, render passes, compute passes, command submission, error scopes.
4. Route browser compositing through the same GPU service primitives, but keep web-exposed WebGPU resources origin-scoped and isolated from browser internals.
5. Provide native backends through existing Simple GPU layers, with a CPU/software fallback for tests and unsupported devices.
6. Add WebGL 1/2 compatibility after Canvas 2D so existing Three.js/Babylon/WebGL content works while WebGPU matures.

---

## 3. Milestone Roadmap (M13–M32)

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
13. WebGPU/WGSL and WebGL compatibility
14. Browser chrome/interface and profile system
15. Accessibility, automation, release hardening

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
- Implement browser chrome shell: tab strip, omnibox, back/forward/reload/stop, downloads entry point, page security indicator, settings/profile menu
- Split ChromiumEngine into browser thread (chrome, navigation, tabs) + renderer thread (DOM, layout, paint, composite)
- Message-passing bridge between threads (post-message style)
- Canvas 2D API: `getContext('2d')`, path operations (moveTo, lineTo, arc, bezierCurveTo), fill/stroke, drawImage, text rendering, pixel manipulation (getImageData/putImageData)
- `<canvas>` element in DOM
- Wire canvas to GPU raster pipeline

**Gate:** Canvas 2D passes canvas2d WPT basic tests. Thread isolation: renderer crash doesn't kill browser chrome (inject fault, verify recovery). Chart.js demo renders. Tabs, omnibox navigation, history entry creation, reload/stop, and session restore pass UI smoke tests.

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

### M25 — WebGPU MVP & WGSL Validation

**Goal:** Modern GPU API available to secure pages with enough functionality for real WebGPU samples.

**Current progress (2026-05-12):**
- Canonical browser WebGPU types added under `src/lib/gc_async_mut/gpu/browser_engine/webgpu_types.spl`.
- Canonical browser WebGPU context added under `src/lib/gc_async_mut/gpu/browser_engine/webgpu_context.spl`.
- Secure-context gate, adapter/device negotiation, feature validation, preferred canvas format, canvas configuration, WGSL stage validation, render pipeline handles, and compute pipeline handles are covered by `test/web_platform/webgpu/webgpu_context_spec.spl`.
- Script canvas API now exposes a tested WebGPU context wrapper via `canvas_get_context_webgpu`, and Canvas 2D mutating operations are covered through method-based state mutation in `test/unit/browser/script/canvas_api_spec.spl`.
- Script navigator API now exposes `navigator_gpu`/metadata helpers, imports through the script module and script runner prelude, and validates secure/insecure `navigator.gpu` behavior in `test/unit/browser/script/navigator_api_spec.spl`.
- Browser WebGPU resource primitives now cover deterministic buffer, texture, sampler, bind group layout, and bind group handles with descriptor/resource validation in `src/lib/gc_async_mut/gpu/browser_engine/webgpu_resources.spl`, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`.
- Browser WebGPU bind group validation now explicitly rejects unsupported layout visibility/type values, duplicate bind group entries, and negative bind group entry bindings before allocating handles, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`.
- Browser WebGPU command primitives now cover render pass recording, compute pass recording, transfer copy recording, queue writeBuffer/writeTexture recording, resource-aware transfer usage/bounds validation, command-buffer finish validation, and queue submission in `src/lib/gc_async_mut/gpu/browser_engine/webgpu_commands.spl`, covered by `test/web_platform/webgpu/webgpu_commands_spec.spl`.
- Browser WebGPU queue submission is now atomic for mixed valid/invalid command-buffer batches, covered by `test/web_platform/webgpu/webgpu_commands_spec.spl`.
- Browser WebGPU status primitives now cover error scopes, uncaptured errors, and device-lost state in `src/lib/gc_async_mut/gpu/browser_engine/webgpu_status_errors.spl`, covered by `test/web_platform/webgpu/webgpu_status_errors_spec.spl`.
- Browser WebGPU device loss now clears pending error scopes, marks adapters unavailable, and blocks new context-level error-scope/report operations after loss, covered by `test/web_platform/webgpu/webgpu_status_errors_spec.spl` and `test/web_platform/webgpu/webgpu_context_spec.spl`.
- Browser WebGPU context now owns a resource table, vends command encoders, routes resource-aware queue submit/writeBuffer operations, exposes validation error scopes, blocks command creation after device loss, and drives deterministic executor-backed compute/texture upload coverage, covered by `test/web_platform/webgpu/webgpu_context_spec.spl`.
- Browser WebGPU deterministic software executor now replays queue writes, render passes, compute dispatches, transfer copies, buffer/texture state checksums, and invalid sequencing into testable counters in `src/lib/gc_async_mut/gpu/browser_engine/webgpu_software_executor.spl`, covered by `test/web_platform/webgpu/webgpu_software_executor_spec.spl`.
- BrowserSession now exposes secure-context `window.isSecureContext`, `navigator.gpu` metadata, and a promise-shaped `navigator.gpu.requestAdapter()` software-adapter result to normal page scripts while hiding `navigator.gpu` from insecure HTTP pages, covered by `test/unit/lib/common/web/browser_session_spec.spl`.
- Script worker models now inherit secure-context navigator/WebGPU availability from their owner context, expose a deterministic `WorkerGlobalScope` model for `isSecureContext`, `navigator`, and `self.postMessage`, and block insecure workers from adapter requests, covered by `test/unit/browser/script/worker_api_spec.spl`.
- JS transpilation now recognizes narrow Worker construction, page-to-worker `postMessage`/`terminate`, WorkerGlobalScope `self.postMessage`, and empty for-of blocks, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- Browser WebGPU adapter/device negotiation now reports adapter availability, fallback compatibility mode, unsupported required features, and unsupported required limits without readying the device, covered by `test/web_platform/webgpu/webgpu_context_spec.spl`.
- Browser WebGPU canvas configuration now covers preferred format, alpha modes, and deterministic present/swapchain progression through the script wrapper and core context, covered by `test/unit/browser/script/canvas_api_spec.spl` and `test/web_platform/webgpu/webgpu_context_spec.spl`.
- Browser WebGPU WGSL validation now rejects GLSL syntax, unbalanced braces, missing stages, and missing MVP stage-interface declarations for vertex position, fragment location, and compute workgroup size, covered by `test/web_platform/webgpu/webgpu_context_spec.spl`.
- Browser WebGPU shader module and pipeline creation now require device readiness, reject device-lost contexts distinctly, and propagate pipeline validation failures into context `last_error`, covered by `test/web_platform/webgpu/webgpu_context_spec.spl`.
- Browser script execution now captures transpiled JavaScript console output through the generated script wrapper and preserves per-entry console levels in the `ScriptHost` console buffer, covered by `test/browser_engine/script/script_host_spec.spl`.
- Browser WebGPU resource creation through the device context now enforces negotiated buffer and texture limits before allocating resource handles, covered by `test/web_platform/webgpu/webgpu_context_spec.spl`.
- Existing nogc WebGPU 3D backend handle-allocation semantics were fixed so `test/lib/nogc_sync_mut/engine/render/webgpu_backend3d_spec.spl` passes.
- Existing nogc WebGPU 3D backend command recording now rejects invalid pass handles, invalid resources, nested passes, negative slots, and non-positive draw counts before enqueueing commands, covered by `test/lib/nogc_sync_mut/engine/render/webgpu_backend3d_spec.spl`.

**Work:**
- Add a real `WorkerGlobalScope` runtime bootstrap once worker script execution is promoted beyond the current message-queue model.
- Expand WGSL validation from the current MVP stage-interface checks toward full W3C grammar coverage.
- Harden remaining sampler descriptor edge cases against CTS coverage and native backend integration.
- Add CPU/software backend for deterministic tests and native GPU backend for smoke/perf.

**Gate:** WebGPU CTS MVP subset passes for shader creation, device negotiation, render pipeline triangle, compute pipeline buffer transform, texture sampling, bind group validation, and error scopes. A secure local demo renders a WGSL triangle and a compute shader writes verified output.

---

### M26 — WebGPU 3D Shading & GPU Compositor

**Goal:** WebGPU supports practical 3D scenes and the browser compositor uses the same hardened GPU service boundary.

**Current progress (2026-05-12):**
- M26 texture descriptor validation has started: 3D texture dimensions, MSAA sample-count constraints, mip-level constraints, texture arrays, and cubemap layer/shape rules are covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`.
- M26 indirect draw command recording has started: render passes now record `drawIndirect`/`drawIndexedIndirect`, validate indirect buffer usage/alignment/ranges, and replay deterministic executor counters through `test/web_platform/webgpu/webgpu_commands_spec.spl` and `test/web_platform/webgpu/webgpu_software_executor_spec.spl`.
- M26 WGSL diagnostics have started: invalid shader modules now produce structured severity, stage, line, column, and formatted diagnostic text for console/DevTools surfaces, with canvas wrapper access and console-buffer emission covered by `test/web_platform/webgpu/webgpu_context_spec.spl`, `test/unit/browser/script/canvas_api_spec.spl`, and `test/unit/browser/script/console_api_spec.spl`.
- M26 render pass descriptor recording has started: command streams now preserve color attachment count, depth/stencil attachment texture id, and attachment dimensions for color+depth and depth-only passes, with deterministic executor replay coverage in `test/web_platform/webgpu/webgpu_commands_spec.spl` and `test/web_platform/webgpu/webgpu_software_executor_spec.spl`.
- M26 WGSL reflection has started: shader sources with `@group`/`@binding` declarations now expose stage-visible resource metadata for uniform buffers, textures, and samplers, including comment skipping and `@binding`/`@group` attribute order variants, covered by `test/web_platform/webgpu/webgpu_context_spec.spl`.
- M26 pipeline layout validation has started: render pipeline creation can now validate reflected WGSL resource bindings against explicit bind group layouts, including missing bindings, stage visibility, and resource type mismatches, covered by `test/web_platform/webgpu/webgpu_context_spec.spl`.
- M26 automatic render pipeline layout derivation has started: reflected WGSL resource bindings can now create deterministic bind group layouts for buffer, texture, sampler, storage buffer, and storage texture resources, merge vertex/fragment visibility for shared bindings, and reject sparse groups, unsupported resources, or incompatible same-binding resource types, covered by `test/web_platform/webgpu/webgpu_context_spec.spl`.
- M26 canvas-facing WebGPU auto-layout has started: `CanvasWebGPUContext` now exposes automatic render pipeline layout creation for secure page-level WebGPU flows, covered by `test/unit/browser/script/canvas_api_spec.spl`.
- M26 script-facing WebGPU auto-layout has started: the JS transpiler now maps compact `createRenderPipeline({ layout: "auto", vertex: { module }, fragment: { module } })` calls and the explicit shorthand to the Simple canvas/core auto-layout wrapper, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 bind group pass recording has started: command encoders can now validate bind group existence, layout dynamic-offset counts, offset alignment, and buffer bounds against the live resource table while recording passes, with canvas command coverage in `test/web_platform/webgpu/webgpu_commands_spec.spl` and `test/unit/browser/script/canvas_api_spec.spl`.
- M26 canvas-facing bind group resources have started: `CanvasWebGPUContext` now exposes bind group layout and bind group creation without requiring page-level flows to reach into the internal resource table, covered by `test/unit/browser/script/canvas_api_spec.spl`.
- M26 script-facing bind group resources have started: the JS transpiler now maps `createBindGroupLayout`, `createBindGroup`, `setBindGroup`, and dynamic-offset bind group calls to the Simple WebGPU wrapper names, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 canvas/script 3D texture access has started: dimension-aware texture creation is now exposed through `CanvasWebGPUContext` and the JS transpiler so page-level flows can create validated 3D textures, covered by `test/unit/browser/script/canvas_api_spec.spl` and `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 storage resource layout ergonomics have started: bind group layout entries now have explicit readonly storage buffer and storage texture constructors matching the validator and auto-layout binding types, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`.
- M26 texture view resources have started: WebGPU resource tables now allocate deterministic texture view handles with format, mip range, array-layer range, and cubemap validation, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`.
- M26 canvas/script texture view access has started: `CanvasWebGPUContext` exposes texture view creation and the JS transpiler lowers `createTextureView(...)` for page-level 3D texture view flows, covered by `test/unit/browser/script/canvas_api_spec.spl` and `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 bind group texture view binding has started: bind group entries can now reference validated texture view handles for sampled/storage texture layout entries while preserving existing texture-handle compatibility, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`.
- M26 render pass texture view attachments have started: render pass color and depth/stencil descriptors can now reference validated texture view handles while recording underlying attachment metadata, covered by `test/web_platform/webgpu/webgpu_commands_spec.spl`.
- M26 canvas/script render pass texture view ergonomics have started: secure canvas wrappers can record render passes with texture view attachments and the JS transpiler lowers `beginRenderPassWithDescriptor(...)` plus attachment `textureView(...)` factories, covered by `test/unit/browser/script/canvas_api_spec.spl` and `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 mip-level texture allocation has started: WebGPU texture handles now preserve allocated mip counts, texture views reject unallocated mip ranges, and canvas/script wrappers expose mip-level texture creation, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`, `test/web_platform/webgpu/webgpu_context_spec.spl`, `test/unit/browser/script/canvas_api_spec.spl`, and `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 descriptor texture allocation has started: browser WebGPU context/canvas/script paths now expose full texture descriptor creation with explicit mip and sample counts for MSAA allocation, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`, `test/web_platform/webgpu/webgpu_context_spec.spl`, `test/unit/browser/script/canvas_api_spec.spl`, and `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 browser-style WebGPU texture descriptors have started: the JS transpiler now lowers `createTexture({ ... })` descriptor objects, including `size: [width, height, layers]`, into descriptor-complete texture allocation calls with WebGPU defaults for optional fields, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 browser-style WebGPU texture view descriptors have started: the JS transpiler now lowers descriptor-object `createTextureView({ ... })` bridges and `texture.createView({ ... })` calls into validated texture view allocation, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 browser-style WebGPU bind group descriptors have started: the JS transpiler now lowers descriptor-object `createBindGroupLayout({ ... })` and `createBindGroup({ ... })` calls into existing validated bind group resource creation, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 browser-style WebGPU render pass descriptors have started: the JS transpiler now lowers descriptor-object `beginRenderPass({ colorAttachments, depthStencilAttachment })` calls into the validated render-pass descriptor path, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 browser-style WebGPU texture upload descriptors have started: the JS transpiler now lowers `queueWriteTexture({ texture }, data, layout, [width, height, layers])` calls into the validated queue texture upload path, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 browser-style WebGPU texture copy descriptors have started: the JS transpiler now lowers `copyTextureToTexture({ texture: source }, { texture: destination }, [width, height, layers])` calls into the validated texture copy command path, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 browser-style WebGPU buffer descriptors have started: the JS transpiler now lowers `createBuffer({ label, size, usage })` descriptor objects into validated buffer allocation, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 browser-style WebGPU sampler descriptors have started: the JS transpiler now lowers `createSampler({ ... })` descriptor objects into validated sampler allocation with WebGPU defaults, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 descriptor-complete WebGPU samplers have started: sampler handles now preserve `addressModeW`, `mipmapFilter`, LOD clamp, compare function, and anisotropy fields with validation, canvas wrappers expose those descriptors, and script descriptor lowering forwards those browser fields, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`, `test/unit/browser/script/canvas_api_spec.spl`, and `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 WebGPU sampler layout validation has started: bind group layouts now distinguish filtering, non-filtering, and comparison sampler bindings, reject incompatible sampler descriptors, and export those layout types through the browser-engine facade, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl` and `test/web_platform/webgpu/webgpu_facade_spec.spl`.
- M26 browser-style WebGPU bind group layout entries have started: the JS transpiler now lowers descriptor-array buffer, texture, storage texture, filtering sampler, non-filtering sampler, and comparison sampler entries into validated Simple layout entry factories, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 browser-style WebGPU bind group resource entries have started: the JS transpiler now lowers descriptor-array buffer, texture, texture view, and sampler resource entries into validated Simple bind group entry factories, covered by `test/unit/browser/script/js_transpiler_spec.spl`.
- M26 WebGPU buffer binding ranges have started: bind group buffer entries now preserve descriptor `offset`/`size`, validate ranges against buffer size, and dynamic offset validation accounts for the base binding offset, covered by `test/web_platform/webgpu/webgpu_resources_spec.spl`, `test/web_platform/webgpu/webgpu_commands_spec.spl`, and `test/unit/browser/script/js_transpiler_spec.spl`.

**Work:**
- Implement depth/stencil attachment semantics, native MSAA allocation, mip generation/use, texture arrays, cubemaps where supported, instancing, uniform/storage buffers, dynamic offsets, and indirect draw where backend supports it.
- Add shader reflection/diagnostics for WGSL errors surfaced to DevTools console.
- Route CSS transforms, opacity, filters, video/canvas layers, and scrolling through a retained GPU layer tree with damage tracking.
- Add frame pacing, vsync, GPU memory budgeting, context loss/recovery, and fallback to software compositing.
- Add sample coverage for Three.js/Babylon WebGPU paths where their feature requirements are supported.

**Gate:** WebGPU 3D sample suite renders pixel-stable triangles, textured cube, instancing, post-processing, and compute particles. Compositor scrolls/top-site pages at target frame budget without repainting unchanged layers.

---

### M27 — WebGL 1/2 Compatibility

**Goal:** Existing WebGL content runs, including common libraries and legacy 3D sites.

**Current progress (2026-05-12):**
- M27 WebGL compatibility has started in pure Simple with a separate `webgl_context.spl` API model. `canvas.getContext` now recognizes `webgl`, `experimental-webgl`, and `webgl2`; initial tests cover context creation, GL error state, context loss/restore, deterministic buffer/texture IDs, shader source/compile validation, and program link/use.
- M27 WebGL shader/program deletion has started: shader and program delete status is queryable, deleted shaders reject source/compile/attach commands, and deleted programs clear current program plus stored uniform values.
- M27 WebGL shader detachment has started: programs can detach attached shader stages, attached-shader counts update, and relinking fails once a required stage is missing.
- M27 WebGL attached-shader introspection has started: programs can return attached shader handles, including deleted-but-still-attached shader lifecycle state.
- M27 WebGL shader precision queries have started: vertex/fragment shader precision formats expose deterministic float and integer range/precision metadata and validate enum/context-loss behavior.
- M27 WebGL explicit program validation has started: `validateProgram`-style checks update `VALIDATE_STATUS`, info logs, and invalid-program errors independently from link/use.
- M27 WebGL object probes have started: shader/program IDs can be tested for live browser object validity and return false after deletion or context loss.
- M27 WebGL shader-source introspection has started: valid shaders return their last assigned GLSL source while deleted, unknown, and context-lost shaders follow browser error/default behavior.
- M27 WebGL vertex attribute offset queries have started: `getVertexAttribOffset` returns configured pointer offsets and validates index/pname errors.
- M27 WebGL buffer parameter queries have started: bound buffers expose `BUFFER_SIZE` and `BUFFER_USAGE` with WebGL target, pname, and no-binding error behavior.
- M27 WebGL texture parameter queries have started: bound textures expose min/mag filter and wrap state through `getTexParameter` with pname and no-binding validation.
- M27 WebGL renderbuffer parameter queries have started: bound renderbuffers expose internal format, width, and height with target, pname, and no-binding validation.
- M27 WebGL framebuffer attachment queries have started: framebuffer attachments expose object type/name and texture attachment metadata with target, attachment, pname, and default-framebuffer validation.
- M27 WebGL resource object probes have started: buffer, texture, framebuffer, and renderbuffer IDs can be tested for live object validity and return false while context is lost.
- M27 WebGL resource deletion has started: buffer, texture, framebuffer, and renderbuffer deletion invalidates resource probes, clears active bindings, and removes stale attribute/framebuffer references.
- M27 WebGL pixel readback has started: `readPixels` returns deterministic packed pixel bytes, honors `PACK_ALIGNMENT`, and validates arguments, framebuffer completeness, and context loss.
- M27 WebGL drawing-buffer introspection has started: contexts expose drawing buffer width and height for renderer/library sizing logic.
- M27 WebGL context attributes have started: contexts expose deterministic browser-style attributes for alpha, depth, stencil, antialias, premultiplied alpha, preserveDrawingBuffer, power preference, and performance-caveat behavior.
- M27 WebGL pixel-store parameter queries have started: `getParameter` now exposes pack and unpack alignment state used by texture uploads and readback.
- M27 WebGL line-width state has started: contexts expose `lineWidth`, current `LINE_WIDTH`, and the deterministic aliased line-width range for WebGL library state sync.
- M27 WebGL front-face state has started: contexts expose `frontFace`, `FRONT_FACE`, and clockwise/counter-clockwise validation for material culling compatibility.
- M27 WebGL polygon-offset state has started: contexts expose `POLYGON_OFFSET_FILL`, factor, and units through capability and parameter queries for z-fighting mitigation paths.
- M27 WebGL sample-coverage state has started: contexts expose sample coverage capabilities, clamped coverage values, and invert state for multisample-compatible render setup.
- M27 WebGL dither capability state has started: contexts now default `DITHER` on and expose enable/disable plus `getParameter` state like browser WebGL.
- M27 WebGL blend-color state has started: contexts expose clamped `blendColor`, `BLEND_COLOR`, and constant-color/alpha blend factors for material blending compatibility.
- M27 WebGL implementation limit queries have started: contexts expose deterministic texture/renderbuffer/viewport limits plus color, depth, stencil, and subpixel bit-depth parameters.
- M27 WebGL renderer identity and shader-limit queries have started: contexts expose vendor, renderer, WebGL/GLSL version strings, compressed-texture format lists, and shader texture/uniform/varying limits for renderer startup probes.
- M27 WebGL canvas bridge state coverage has started: script canvas wrappers now expose context attributes, `getParameter`, `isEnabled`, `disable`, line width, front-face, polygon offset, sample coverage, and blend color state.
- M27 WebGL JS transpiler state coverage has started: browser-style `getParameter`, `getContextAttributes`, `isEnabled`, `disable`, `lineWidth`, `frontFace`, `polygonOffset`, `sampleCoverage`, and `blendColor` calls now lower to canvas WebGL helpers with matching constants.
- M27 WebGL canvas readback bridge has started: script canvas wrappers and JS lowering now expose `getError`, `pixelStorei`, `readPixels`, pack/unpack alignment constants, and RGB readback constants.
- M27 WebGL JS capability-query constants have started: renderer identity, shader-language version, line-width range, compressed-format list, viewport, texture, renderbuffer, shader, varying, and channel-depth query constants are now available to transpiled scripts.
- M27 WebGL framebuffer/renderbuffer script bridge has started: canvas wrappers and JS lowering now expose framebuffer/renderbuffer creation, binding, storage, attachment, status, and attachment/renderbuffer parameter queries.
- M27 WebGL indexed draw script bridge has started: canvas wrappers and JS lowering now expose `drawElements`, `LINES`, `UNSIGNED_SHORT`, and `UNSIGNED_INT` for element-array-buffer rendering paths.
- M27 WebGL resource lifecycle script bridge has started: canvas wrappers and JS lowering now expose `is*` probes and `delete*` cleanup for buffers, textures, framebuffers, and renderbuffers.
- M27 WebGL shader/program lifecycle script bridge has started: canvas wrappers and JS lowering now expose shader/program info logs, validation, detach, attached shader queries, delete operations, and `DELETE_STATUS`.
- M27 WebGL shader precision/reflection script bridge has started: canvas wrappers and JS lowering now expose `getShaderPrecisionFormat` plus shader/program reflection constants for shader type, info-log length, attached shaders, active uniforms/attributes, current program, precision classes, vector/matrix, and sampler types.
- M27 WebGL fixed-function state script bridge has started: canvas wrappers and JS lowering now expose depth, stencil, blend, scissor, color/depth/stencil masks, and separate blend/stencil controls backed by `getParameter` round trips.
- M27 WebGL separate stencil state has started: contexts, render command IR, canvas wrappers, and JS lowering now expose `stencilFuncSeparate`, `stencilOpSeparate`, and back-face stencil query constants.
- M27 WebGL texture mutation script bridge has started: canvas wrappers and JS lowering now expose `getTexParameter`, `texSubImage2D`, and `generateMipmap` so script textures can query parameters, update regions, and mark mipmap generation.
- M27 WebGL framebuffer copy texture script bridge has started: contexts, canvas wrappers, and JS lowering now expose `copyTexImage2D` and `copyTexSubImage2D` for framebuffer-to-texture update paths.
- M27 WebGL blend conformance has started: contexts now reject mixed constant-color and constant-alpha blend factors with `INVALID_OPERATION`, preserve prior blend state, and expose blend constants through the browser-engine facade, covered by `test/web_platform/webgl/webgl_context_spec.spl` and `test/web_platform/webgl/webgl_facade_spec.spl`.
- M27 WebGL command synchronization script bridge has started: contexts, render command IR, canvas wrappers, and JS lowering now expose `flush` and `finish` for renderer synchronization points.
- M27 WebGL compressed texture script bridge has started: canvas wrappers and JS lowering now expose `compressedTexImage2D` and `compressedTexSubImage2D`, with context validation preserving the advertised empty compressed-format set instead of silently accepting unsupported formats.
- M27 WebGL context recovery script bridge has started: canvas wrappers and JS lowering now expose context loss/restoration hooks so renderer recovery paths can observe `CONTEXT_LOST_WEBGL` and resume after restoration.
- M27 WebGL hint state script bridge has started: contexts, render command IR, canvas wrappers, and JS lowering now expose `hint`, `GENERATE_MIPMAP_HINT`, and quality constants for texture-generation tuning paths.
- M27 WebGL clear and viewport query bridge has started: canvas constants and JS lowering now expose `COLOR_CLEAR_VALUE` and `VIEWPORT` so script render setup can round-trip clear color and viewport state through `getParameter`.
- M27 WebGL2 draw/read buffer coverage has started: contexts, render command IR, canvas wrappers, and JS lowering now expose `drawBuffers`, `readBuffer`, `DRAW_BUFFER0`, `READ_BUFFER`, and `MAX_DRAW_BUFFERS` for single-color-target framebuffer render/readback paths.
- M27 WebGL2 vertex array object coverage has started: contexts, render command IR, canvas wrappers, and JS lowering now expose create/bind/delete/probe vertex array operations with attribute and element-array-buffer state restoration.
- M27 WebGL2 sampler object coverage has started: contexts, render command IR, canvas wrappers, and JS lowering now expose sampler create/bind/delete/probe plus parameter mutation/query state for texture-unit sampling setup.
- M27 WebGL packed texture type coverage has started: texture upload/readback validation, canvas wrappers, and JS lowering now expose `UNSIGNED_SHORT_5_6_5`, `UNSIGNED_SHORT_4_4_4_4`, and `UNSIGNED_SHORT_5_5_5_1` with correct RGB/RGBA byte counts.
- M27 WebGL texture parameter enum coverage has started: canvas wrappers and JS lowering now expose mipmap min filters and `MIRRORED_REPEAT` so script texture setup can use the browser WebGL enum set already validated by the context.
- M27 WebGL active texture script bridge has started: canvas wrappers and JS lowering now expose `activeTexture`, `TEXTURE0`, `ACTIVE_TEXTURE`, and `TEXTURE_BINDING_2D` so library texture-unit selection can be observed through `getParameter`.
- M27 WebGL cube-map texture coverage has started: contexts, canvas wrappers, JS lowering, and GLSL reflection now expose cube-map binding/query constants, cube-face `texImage2D` targets, and `samplerCube` uniforms for skybox/environment-map setup paths.
- M27 WebGL culling state script bridge has started: canvas wrappers and JS lowering now expose `cullFace` and `CULL_FACE_MODE` so renderer material-side setup can round trip through browser-style state queries.
- M27 WebGL clear/depth range script bridge has started: canvas wrappers and JS lowering now expose `clearDepth`, `depthRange`, `clearStencil`, `DEPTH_CLEAR_VALUE`, and `DEPTH_RANGE` for complete clear-state setup.
- M27 WebGL buffer/attribute query script bridge has started: canvas wrappers and JS lowering now expose buffer parameter queries, vertex attribute queries/offsets, attribute disable, and active attribute reflection.
- M27 WebGL generic vertex attribute state has started: contexts, canvas wrappers, and JS lowering now expose `vertexAttrib4f` plus `CURRENT_VERTEX_ATTRIB` queries for constant attribute setup paths.
- M27 WebGL generic vertex attribute convenience setters have started: contexts, canvas wrappers, and JS lowering now expose `vertexAttrib1f`, `vertexAttrib2f`, and `vertexAttrib3f` mapped onto browser-style current attribute values.
- M27 WebGL generic vertex attribute array setters have started: contexts, canvas wrappers, and JS lowering now expose `vertexAttrib1fv`, `vertexAttrib2fv`, `vertexAttrib3fv`, and `vertexAttrib4fv` through the shared current-attribute render command path.
- M27 WebGL packed vertex attribute coverage has started: `vertexAttribPointer` now accepts byte, unsigned-byte, short, unsigned-short, and float attribute types with stride/offset alignment validation for packed geometry buffers.
- M27 WebGL vector uniform coverage has started: contexts, canvas wrappers, JS lowering, and backend command IR now expose `uniform2f`, `uniform3f`, `uniform2fv`, `uniform3fv`, and `uniform4fv` for vector shader parameters used by 3D libraries.
- M27 WebGL scalar uniform array coverage has started: contexts, render command IR, canvas wrappers, and JS lowering now expose `uniform1fv` for float uniforms passed through array-backed library state.
- M27 WebGL integer uniform coverage has started: contexts, render command IR, canvas wrappers, JS lowering, and GLSL reflection now expose `int`, `ivec2`, `ivec3`, `ivec4`, plus `uniform2i`, `uniform3i`, and `uniform4i` for integer shader state.
- M27 WebGL uniform query coverage has started: contexts, canvas wrappers, and JS lowering now expose `getUniform` for default and stored shader uniform values used by renderer state sync.
- M27 WebGL context metadata script bridge has started: canvas wrappers and JS lowering now expose supported extensions, context-loss state, and drawing-buffer dimensions for common renderer capability checks.
- M27 WebGL backend command coverage has started: `enable()`/`disable()`, `scissor()`, `activeTexture()`, `pixelStorei()`, `readPixels()`, scalar/vector uniform setters, buffer data and vertex-attribute setup, generic vertex attributes, texture parameter/upload/update/mipmap operations, framebuffer/renderbuffer setup, `lineWidth()`, `depthFunc()`, `cullFace()`, `frontFace()`, `blendColor()`, `blendFuncSeparate()`, `blendEquationSeparate()`, `polygonOffset()`, `sampleCoverage()`, clear-depth/stencil, depth-range, color/depth masks, stencil masks, and stencil test ops now record render commands after state validation so capability toggles, backend clipping, geometry setup, texture-unit replay, texture/framebuffer replay, blend-state replay, stencil replay, uniform replay, readback replay, and draw-state replay can follow browser WebGL state changes.

**Work:**
- Expand `canvas.getContext("webgl")`, `webgl2`, shader compile/link, GL state machine, buffers, textures, framebuffers, uniforms, attributes, extensions baseline.
- Translate GLSL ES to backend shader representation or route through existing GPU backend where available.
- Provide ANGLE-like conformance mapping for validation, error behavior, context loss, and extension exposure.
- Keep WebGL and WebGPU resource/security models separate.

**Gate:** WebGL conformance basic suite passes, Three.js WebGL examples render, context loss tests pass, and WebGL content cannot access cross-origin pixels without CORS approval.

---

### M28 — Browser Profile, Permissions & UX Completion

**Goal:** The browser feels complete for daily use.

**Work:**
- Persistent profiles: history, bookmarks, downloads, cookies, storage, cache, preferences.
- Permission prompts and per-origin settings for geolocation, camera/microphone hooks, notifications, clipboard, downloads, popups, autoplay, WebGPU high-performance adapter.
- Password/autofill storage hooks with encrypted-at-rest backend boundary.
- Find-in-page, zoom, print/PDF path, page source, save page, responsive/mobile emulation, clear browsing data.
- Accessibility tree, focus traversal, keyboard navigation, ARIA role/name/state mapping.

**Gate:** Browser UI smoke covers tabs, profiles, history, bookmarks, downloads, permissions, zoom, find, print preview, session restore, keyboard-only navigation, and accessibility tree snapshots.

---

### M29 — Automation, WebDriver BiDi & Full DevTools

**Goal:** Browser is testable and debuggable with external tooling.

**Work:**
- Complete CDP domains from M23 and add WebDriver BiDi session, browsingContext, script, network, log, input, and screenshot support.
- Add deterministic screenshot capture, trace export, performance timeline, memory snapshots, GPU frame diagnostics.
- Add remote debugging auth/bind controls so DevTools is safe by default.

**Gate:** Playwright/Selenium smoke can launch Simple Browser, navigate, click, evaluate JS, intercept network, capture screenshots, and close cleanly. Chrome DevTools frontend remains compatible.

---

### M30 — Privacy, Safe Browsing & Enterprise Hardening

**Goal:** Production security posture beyond sandboxing.

**Work:**
- Tracking prevention controls, partitioned storage, third-party cookie policy, private browsing profile.
- Safe-browsing style malicious URL/download checks through a pluggable provider interface.
- Certificate UI, HSTS, certificate transparency hooks where feasible, client cert hooks.
- Policy/config system for locked settings, proxy, certificates, extension/API toggles.

**Gate:** Security regression suite covers storage partitioning, private browsing cleanup, mixed content, CSP, SRI, HSTS, permission persistence/revocation, malicious download blocking hook, and policy override behavior.

---

### M31 — Extensions & User Scripts

**Goal:** Controlled browser extension surface and Simple Script/user-script automation.

**Work:**
- Implement a minimal extension manifest model, content scripts, isolated worlds, message passing, storage, browser action UI, and permissions.
- Support Simple Script and JavaScript user scripts with explicit per-origin grants.
- Expose stable automation APIs without giving extensions direct engine internals.

**Gate:** Extension smoke loads a content script, modifies DOM in isolated world, exchanges messages with a background worker, persists extension storage, and respects host permissions.

---

### M32 — Release Candidate & Production Readiness

**Goal:** Ship-quality browser build.

**Work:**
- Freeze compatibility scope, close release blockers, run full WPT selected corpus, WebGPU CTS selected corpus, Test262 selected corpus, top-site screenshot corpus, security suite, performance suite, memory leak suite, accessibility suite, and packaging checks.
- Build native release artifacts, crash reporter hooks, updater hooks, profile migration, telemetry-off-by-default diagnostics export.
- Document unsupported APIs and compatibility flags.

**Gate:** Release candidate has zero critical/high security bugs, no known crashers in top-site corpus, WPT/Test262/WebGPU CTS targets met, startup/render/navigation budgets met, renderer/GPU crash recovery verified, and profile data survives upgrade/downgrade tests.

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
| 16 | WebGPU demos/apps | WebGPU + WGSL + secure canvas | M25 |
| 17 | Three.js/Babylon 3D | WebGL/WebGPU + GPU compositor | M26/M27 |

**Cumulative top-20 coverage by milestone:**

| Milestone | Top-20 Coverage | Cumulative Sites |
|-----------|----------------|-----------------|
| M12 (current) | 14/20 (70%) | 14 existing corpus matches |
| M15 | 15/20 (75%) | +DuckDuckGo |
| M16 | 16/20 (80%) | +Yahoo Japan |
| M17 | 17/20 (85%) | +Microsoft Online |
| M20 | 19/20 (95%) | +Pornhub, XVideos |
| M21 | 20/20 (100%) | +XHamster |
| M25 | 20/20 + WebGPU demos | +secure WebGPU sample class |
| M27 | 20/20 + WebGL 3D corpus | +legacy 3D/library compatibility |

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

### R11: WebGPU Security and Driver Variance
**Impact:** High — WebGPU exposes modern GPU resources to untrusted web content and depends on backend driver behavior.
**Mitigation:** M25 requires secure-context gating, strict WGSL validation, feature/limit negotiation, error scopes, device-loss handling, origin-scoped resources, GPU process isolation before broad exposure, and CPU fallback tests.

### R12: Chrome-Class Scope Explosion
**Impact:** High — trying to ship every Chrome feature at once can stall the project.
**Mitigation:** Each milestone has a compatibility gate and release-quality stop condition. Proprietary services are out of scope; standards compatibility and usable browser workflows are in scope.

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
| webgpu backend/context | src/lib/gc_async_mut/gpu + api guides | TBD | M25 | M19, M22 for isolation |
| webgl compatibility | new browser_engine/gpu/webgl | TBD | M27 | M25 |
| browser chrome/profile | app/browser + browser_engine/profile | TBD | M19/M28 | M16 |
| automation/devtools | browser_engine/devtools + app protocol | TBD | M23/M29 | M15, M16 |

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
| M25 | WebGPU CTS MVP subset | WebGPU device, canvas, WGSL, render/compute |
| M27 | WebGL conformance basic subset | WebGL 1/2 state, shaders, textures, context loss |
| M29 | Automation smoke | CDP + WebDriver BiDi launch/navigate/evaluate/screenshot |
| M32 | Release suite | WPT/Test262/WebGPU CTS/top-site/security/perf/accessibility gates |

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
M25  WebGPU MVP + WGSL Validation   ← recent GPU web platform
M26  WebGPU 3D + GPU Compositor     ← modern 3D shading and compositing
M27  WebGL 1/2 Compatibility        ← existing 3D web content
M28  Profile + Permissions + UX     ← daily-driver browser interface
M29  CDP + WebDriver BiDi           ← automation and debugging
M30  Privacy + Safe Browsing        ← production security posture
M31  Extensions + User Scripts      ← controlled customization
M32  Release Candidate              ← ship gate
```

Ordering rationale: Each milestone builds on the previous. Floats and CSS quick wins (M13) are first because they have the highest WPT-per-effort ratio. JS (M15) before networking (M16) because the fetch API binding needs JS runtime. Networking before CSS3 (M17) because CSS3 animations are less impactful than loading real pages. Security hardening (M22) precedes broad WebGPU exposure because untrusted shader/GPU access needs process and origin boundaries. WebGPU/WebGL land after the browser has canvas, threading, security, and DevTools foundations.

---

## 9. Current External References

- W3C WebGPU specification: https://www.w3.org/TR/webgpu/
- W3C WGSL Candidate Recommendation Draft, 2026-05-07: https://www.w3.org/TR/WGSL/
- MDN WebGPU API, checked 2026-05-12: secure-context only and not Baseline across all widely used browsers.
- Chrome WebGPU overview: https://developer.chrome.com/docs/web-platform/webgpu/overview
