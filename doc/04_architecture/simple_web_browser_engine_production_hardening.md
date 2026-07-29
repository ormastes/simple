<!-- codex-architecture -->
# Simple Web Browser Engine Production Hardening Architecture

Status: Proposed

Date: 2026-07-26

Requirements:

- `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- `doc/02_requirements/nfr/simple_web_browser_engine_production_hardening.md`

## Decision

Production browsing uses two trust domains:

1. a browser broker owns chrome, navigation commits, history/bookmarks,
   URL/origin policy, network/TLS, cookies/storage, resource budgets, renderer
   lifecycle, and host capabilities;
2. a site-locked OS-sandboxed renderer owns hostile HTML/CSS/JavaScript,
   canonical DOM/event state, style/layout/paint, and emits a bounded
   `DrawIrComposition`.

The broker validates renderer messages and submits accepted compositions to the
existing persistent Engine2D compositor. Production startup fails if the
platform sandbox cannot be established; it never falls back to executing
hostile pages in-process.

## Existing decisions preserved

- ADR-002 keeps `src/lib/gc_async_mut/gpu/browser_engine/` canonical.
- `BrowserSession` remains navigation/profile state owner.
- Browser/Web semantic/layout producers emit `DrawIrComposition`.
- Engine2D owns device/session execution, text, `FontRenderer`, transient
  `FontRenderBatch`, atlases, and caches.
- Engine3D is not a browser rendering path.
- `examples/11_advanced/browser/**` remains research/fixture code.

## Production flow

```text
Hosted input / UI access
        |
        v
Browser broker (src/app/ui.browser)
  chrome + history + policy + network/TLS + sandbox lifecycle
        |
        | bounded typed IPC: generation, request_id, kind
        v
Site renderer child
  BrowserSession document state
  canonical HTML tree + live DOM + browser-only JS
  events + one clock + style/layout/paint
        |
        | bounded DrawIrComposition
        v
Broker validation -> persistent Engine2dCompositorBackend -> pixels
```

## Component ownership

### Browser broker

Composition root: `src/app/ui.browser/`.

It owns:

- production browser process lifecycle;
- sandboxed renderer spawn/restart and generation numbers;
- committed top-level URL/origin and navigation generation;
- Fetch/CORS/CSP/mixed-content/redirect decisions;
- TLS, HSTS, DNS, response limits, cookie/storage authority;
- bookmarks/home configuration;
- versioned profile persistence outside the hostile renderer;
- renderer IPC validation, resource budgets, crash handling;
- production Engine2D compositor submission and presentation.

Minimal new runtime state:

```text
BrowserRendererProcess
  pid
  generation
  receive_endpoint
  send_endpoint
  restart_window
```

No browser-controller factory, navigation facade, or parallel history owner is
introduced.

### Hosted browser profile

`src/os/hosted/browser_profile_store.spl` owns versioned SQLite persistence
above BrowserSession. It stores bounded bookmark and wall-clock HSTS snapshots,
while BrowserSession remains the only validator that converts them into live
session state. The hosted entry captures the trusted seeded browser window ID
before processing runtime input and attaches the profile only to that ID;
page-controlled or later app-ID strings cannot acquire or overwrite browser
profile state.

### BrowserSession

`src/lib/gc_async_mut/web/browser_session*.spl` remains the profile/document
state machine. Existing `begin_network_navigation`, `stop_loading`, `reload`,
`go_back`, `go_forward`, `go_home`, and favorite methods remain canonical.

Required changes:

- replace raw text URL policy with canonical `Url`/`Origin`;
- stamp requests and responses with navigation generation;
- reject late responses after stop/replacement;
- separate address draft from `pending_url`;
- hold the current canonical DOM/render session;
- expose one DOM event dispatch path;
- release document-owned state on navigation/close.

### Canonical URL, origin, network, cookies, and TLS

Reuse `src/lib/gc_async_mut/gpu/browser_engine/net/`:

- `Url` and `Origin` become the only policy identity;
- the broker derives initiator origin from committed state, never renderer IPC;
- Fetch owns redirect/CORS/credentials/abort;
- repeated CORS response fields are combined before policy evaluation, so
  singleton `Access-Control-Allow-Origin` duplicates fail closed;
- CSP is enforced before queuing or executing script/style/connect/image work;
- cookies use the existing network cookie owner extended with host-only,
  expiry, `Secure`, `HttpOnly`, and `SameSite`;
- TLS delegates to a maintained platform provider with SNI and platform trust.
  Linux/FreeBSD hosted browser builds use the opt-in OpenSSL provider through
  `SIMPLE_LINK_OBJECTS`; it is not part of freestanding or ordinary native
  runtime links. Other hosts retain their native platform provider.

The permissive BrowserSession cookie authority is retired after migration.
Production TLS does not use string/CN test verifiers or HTTP fallback.

### Browser-only JavaScript profile

Add one mode to the existing JS runtime:

```text
JsRuntimeProfile.Browser
JsRuntimeProfile.Node
```

`Browser` installs selected web globals only. It never installs `require`,
`process`, `Buffer`, generic FFI/IPC, filesystem, listener, environment, or
process execution. Existing Node consumers opt into `Node`.

BrowserSession is the only production script host. The predictable temporary
file subprocess runner and literal fake-success scanners are disconnected from
production; they are removed when no fixture depends on them.

### Canonical DOM and events

The existing HTML tree builder assigns monotonically increasing,
document-local node IDs. IDs remain stable for the committed document and are
invalid after navigation or structural replacement.

Both canonical DOM parsing and direct render parsing admit at most 65,536
document nodes. BrowserSession detects truncation before replacing the active
document and returns `resource_limit`; direct rendering bounds its arena and
returns the safe parsed prefix.

Canonical tokenization independently admits 262,144 content tokens and 65,536
retained attributes, propagating either truncation through the same atomic
load failure. Direct render parsing rejects payloads above the existing 1 MiB
renderer envelope or 262,144 structural parts before split/event allocation or
degenerate diagnostics.

CSS scanning applies the same source admission, retains at most 4,096 rules per
document, and bounds both opening- and closing-brace split structure before
allocation. Later style blocks consume only the remaining document rule budget;
the first admitted rules remain authoritative. Variable substitution cannot
expand beyond the 1 MiB source envelope or recurse through more than 16 fallback
levels. Each rule retains at most 256 selector groups and 256 selector parts.
Keyframe offset lists and declaration lists retain at most 256 entries.

`common.web.event_types.DomEvent` is the event type. BrowserSession adds:

```text
dispatch_dom_event(event: DomEvent) -> BrowserDomDispatchResult
dispatch_pointer_event(kind, x, y, button) -> BrowserDomDispatchResult
dispatch_key_event(kind, key, key_code, modifiers) -> BrowserDomDispatchResult
set_focused_node(node_id) -> Result<bool, text>
```

Dispatch order is root-to-parent capture, target capture, target bubble, then
parent-to-root bubble. Default actions run once after propagation unless
canceled. Links, inputs, buttons, forms, focus, UI access, JavaScript, and
Simple Script use this path.

The string-based UI link parser and target-only event path are retired.

### Persistent render session

Add one `SimpleWebRenderSession` beside the existing release-measured Simple Web
HTML renderer so it can reuse current private stage functions and types.

This is not another Web IR or pixel cache. It lives with
`simple_web_html_layout_renderer.spl`, retains that renderer's existing
`HNode`/`Rules`/`HtmlChildIndex`/`Style`/`LayoutResult` values, and still emits
the canonical `DrawIrComposition`. The hosted browser worker owns exactly one
session. The compositor's `WebRenderPixelArtifactCache` and
`simple_web_content_revision_with_theme` are not reusable here: they serve the
separate WM pixel path, hash/compare serialized content, include scroll in the
key, and cannot expose semantic-stage invalidation.

`BrowserSession` is the authoritative invalidation owner:

- `BrowserRenderRevisions.document_revision` aliases the existing
  `ui_access_revision`; the missing mutation sites are repaired instead of
  adding a competing DOM counter.
- `style_revision` advances when committed external/inline stylesheet HTML
  changes.
- `resource_revision` advances when the bounded decoded-image set changes.
- `BrowserRenderSnapshot` returns those cheap revisions and serializes HTML
  only when the caller's document or style revision is stale.

`SimpleWebRenderSession` owns `viewport_revision` and
`composition_revision`. Scroll, text-overlay, resource, and animation-time
keys remain inputs to that owner; they do not mutate BrowserSession revisions.
All counters saturate rather than wrap to a cache-valid old value.

State:

- source/document revision and viewport;
- canonical nodes, rule buckets, child index, computed styles, layout;
- current `DrawIrComposition`;
- one event loop, animation controller, render state, and monotonic clock;
- document-bounded per-node CSS animation epochs, swept with the live DOM and
  passed to layout as engine-owned state rather than author-visible markup;
- dirty stage and parse/style/layout/paint counters/timings.

Invalidation:

| Change | Work |
|---|---|
| navigation/source | parse, CSS, style, layout, paint |
| any accepted DOM/title mutation | serialize, parse, CSS, style, layout, paint |
| committed stylesheet text | serialize, parse, CSS, style, layout, paint |
| viewport/media | CSS, style, layout, paint; retain parsed nodes |
| decoded image set | paint only; layout currently does not consume decoded dimensions |
| active CSS animation sample | animated style, layout, paint; retain parse/CSS/base style |
| scroll or caret/selection overlay | scroll/hit/paint only; retain raw layout |
| monotonic time with no due visual change | reuse composition and hit index |
| unchanged frame | reuse composition and hit index |

Initial production scope may repaint the full dirty frame. Partial damage is
deferred until profiling proves it necessary. It may also conservatively
invalidate all style/layout work for a DOM mutation; node-diff/subtree
invalidation is not required for the first retained implementation.

The cache is bounded by the already-enforced document and image limits and
stores one current document stage set, one base-style set, one layout, and one
composition/hit index. Replacement swaps those values rather than appending.
`reset()` drops all retained semantic/layout/composition values on navigation;
`close()` also clears the worker's hit index and image revision list. Process
exit remains the final sandbox-worker release boundary.

The first implementation slice retains the existing combined
`SimpleWebLayoutDrawIrResult` and proves only unchanged-frame reuse plus close
reclamation. It intentionally reruns the full canonical renderer for every
dirty key. The stage-selective rows above remain required follow-ups; no
partial-stage PASS is inferred from the combined-result cache.

The render session emits Draw IR only. The existing persistent
`Engine2dCompositorBackend` creates device/font state once, clears/submits on
dirty frames, and shuts down once. The per-call helper that creates and shuts
down Engine2D remains diagnostic and is forbidden in production hot paths.

### One browser clock

The app reads a monotonic timestamp once per loop and supplies it to the render
session. The same timestamp drives:

1. due timers and microtasks;
2. one rAF callback batch;
3. DOM/script mutations;
4. CSS transition/animation updates;
5. invalidation and one render/present.

Each rAF callback receives that render-opportunity timestamp, not its scheduled
deadline, so delayed frames do not report stale time or accumulate animation lag.

Resume deltas are clamped to 100 ms. A deterministic test clock supplies exact
timestamps. Timer/animation modules do not read wall time independently.

### GC and lifecycle

Ownership is split deliberately:

- profile lifetime: history, bookmarks, cookie/storage partitions;
- document lifetime: DOM, listeners, timers, JS objects, styles, layout,
  composition, images, requests;
- app lifetime: sandbox broker, Engine2D device/font owners.

Navigation/close cancels document work and clears listener, timer, promise,
request, DOM, layout, image, and composition references before installing the
next document. Cached back/forward commits also reset renderer-owned scroll
before painting the restored document. Detached-node animations and completed/canceled timers are
compacted. Engine/device/font state survives same-size navigation and is
released exactly once on app close.

Document warnings are duplicate-suppressed, capped at 128 entries and 4096
bytes per entry at append time, including the in-progress load state before
script/style/WASM finalization. Renderer diagnostics consume only the first 4096 characters
without joining the retained warning set, so timer/animation traffic cannot
turn repeated policy denials into growing retained memory or per-frame work.
Failed child cleanup retries once per second while its window remains live;
successful close drops decoder, network-cache, and history state even when the
lightweight failure tombstone must remain fail closed. Learned HSTS remains
available for the broker's persistence handoff. A child already reaped by the
liveness facade clears its consumed handle before terminal state cleanup;
genuine close failures retain the handle for retry.

Evidence uses real `mem_tracker` live counts/bytes, heap-registry count when
available, RSS, node/listener/timer/layout/command counts, and lifecycle
create/shutdown counters. No synthetic collection or pause counter is added.
The known interpreter GC root-scan blowup remains a separate root-cause fix and
must be included when browser evidence reproduces it.

## Security boundary

Renderer privileges:

- no direct filesystem, environment, process, listener, device, DNS, TLS,
  cookie jar, bookmark, or host UI access;
- inherited typed IPC handles only;
- bounded messages and Draw IR;
- one site per renderer for selected Option B.

Broker rules:

- allow `http`, `https`, and audited internal pages;
- `file` requires a user-selected broker capability limited to an exact root;
- deny `data`, `javascript`, custom, and external handler schemes unless a
  separately audited exact operation is granted;
- reject credential-bearing/control-character URLs and HTTPS downgrade
  redirects;
- validate generation/request IDs, header/body sizes, redirect counts, Draw IR
  commands/strings/images, and late/duplicate replies.

Platform enforcement:

- Linux: an argv-bound ELF preinit stage installs `no_new_privs`, Landlock,
  and startup-safe seccomp before constructors; stage-two admission fails
  unless that marker is active, then adds rlimits and the full worker filter;
- macOS: signed App Sandbox helper/XPC profile;
- Windows: AppContainer plus kill-on-close Job Object and explicit handles.

A warning-only or job-only sandbox does not satisfy production acceptance.

## Failure behavior

- Invalid URL/scheme: no state mutation; `invalid_url`/`unsupported_scheme`.
- TLS/CORS/CSP/mixed-content denial: keep last committed page; show a typed
  error/interstitial without HTTP fallback.
- Stop: cancel pending document/resource/script work and reject late commits.
- Renderer crash/OOM/timeout: discard its generation and in-flight document,
  preserve chrome/profile state, show internal error, and allow at most three
  restarts per minute.
- IPC violation: reject message; repeated violation terminates the renderer.
- Budget violation: terminate only the offending renderer/page.

## Performance and observability

Counters:

- startup and navigation timestamps;
- parse/style/layout/paint counts and microseconds;
- dirty-stage transitions and unchanged-frame reuse;
- timer/rAF/event queue depths;
- input-to-present and frame p50/p95/max;
- nodes, rules, styles, layout boxes, Draw IR commands/images;
- renderer restarts and security denials;
- Engine2D/device/font create/shutdown counts;
- memtrack live count/bytes, heap registry, RSS.

Sensitive values, cookies, tokens, page source, and host paths are not logged.

## Pattern evaluation

- In-process hardening is rejected because it cannot contain renderer
  compromise.
- A new browser framework/factory is rejected; existing BrowserSession,
  network, IPC, runtime sandbox, and Engine2D owners suffice.
- Embedding a mature engine is not selected by Feature Option B.
- No MDSOC weaving is required. Runtime composition at the existing app root
  plus a browser-only JS profile and platform sandbox adapters is smaller and
  easier to audit than a new virtual capsule.

## Verification consequences

Existing parser, CSS, JS, control, and Draw IR tests are supporting evidence.
Production acceptance additionally requires:

- one end-to-end user/render/event/navigation spec;
- one security/TLS/sandbox spec;
- one native performance/GC/lifecycle spec;
- pinned WPT/Test262/fuzz dependencies;
- live Linux proof and separate macOS/Windows rows before platform claims.

SimpleOS QEMU is supporting smoke evidence and cannot prove hosted OS sandbox
or native TLS behavior.

## Open blockers

- duplicate production HTML semantic paths need one measured authority;
- animation code imports research/example style types;
- BrowserSession page code currently receives Node globals and unrestricted
  `file://`;
- Linux now has a fail-closed sanitized renderer launcher, deny-all Landlock,
  seccomp process/network denial, and a persistent BrowserSession/Draw IR
  worker. The broker permits one request in flight, requires exact monotonic
  IDs independently in each direction, requires every renderer fetch/frame to
  name the exact parent request it answers, preserves absolute animation time,
  and closes the contained process on any timeout or protocol failure. Renderer
  network requests and broker responses now use bounded length-prefixed fields;
  the parent alone owns Fetch/TLS and uses a public-address-only, response-capped
  HTTP job while the renderer sandbox remains socketless. Renderer protocol
  traffic now uses a full-duplex inherited fd 0 while ordinary stdout/stderr
  are discarded, and seccomp denies direct System V shared-memory, message,
  semaphore IPC, path metadata and xattr enumeration, modern mount and io_uring
  operations, cross-process memory advice, and kernel-control calls. The
  focused native containment runner is enforced by the browser renderer
  sandbox workflow. Validated renderer frames admit only the HTML producer's
  rectangle/text command subset and enforce frame-wide overdraw, text, style,
  and glyph budgets before Draw IR reaches the parent renderer. Fetch now
  rejects `SameOrigin` mode before cache or transport when the request target
  differs from the committed requester origin, and every cache hit is
  revalidated against the current CORS response policy. The renderer broker
  now requires chrome-issued document requests to exactly consume one
  parent-issued canonical URL/method/header/body permit. Renderer-originated
  links and supported forms receive a separate one-shot permit only after a
  parent-owned committed/provisional origin exists: GET carries no body or
  content type, POST is URL-encoded, credentials are `include`, and no
  renderer-defined headers survive. Existing chrome permits cannot be replaced.
  HSTS upgrades remain broker-generated redirects rather than accepting an
  HTTP/HTTPS split directly. HSTS policy can be learned only inside the
  error-free completed platform HTTPS job branch; generic, cached, mock, HTTP,
  parse-error, and failed-TLS paths cannot supply an authentication boolean or
  seed policy. The broker
  derives resource mode from the broker's committed origin instead of the
  renderer's kind, and authorizes only bounded simple CORS requests until
  preflight uses the public-only broker transport. Redirects receive one exact
  derived successor permit with downgrade and hop-limit enforcement. Typed
  parent-issued open/back/forward/home/reload/stop commands now cross the
  bounded protocol; the broker owns committed URL/origin plus a 256-entry
  history and commits only after a validated renderer frame. A fail-closed
  external-frame compositor seam exists. It owns up to four receiver-indexed
  window/frame pairs, rejects frames that do not match the live content box,
  caps retained external pixels at 16,777,216, invalidates pixels on resize,
  and releases only the closed window's frame. The hosted entry now owns one
  bounded renderer/raster entry per secondary browser window, polls every live
  child once per host tick (including minimized children for cleanup), and
  reconciles destroyed windows through explicit process/network/raster teardown.
  Browser windows without an admitted frame render blank and never fall back to
  parent HTML/JavaScript execution. The broker now also exposes a
  per-tick transaction pump, owns at most one parent HTTP job, and writes each
  queued response with one bounded nonblocking pipe operation per poll. Stop
  clears trusted pending state before cancel/free and issuing its correlated
  renderer command. A broker-derived provisional document origin is shared by
  request policy and FetchEngine to authorize CSS/script/module requests after
  the document response, while committed chrome URL/history still wait for a
  validated frame; legacy synchronous calls wrap that same pump.
  Production chrome now uses the broker for Stop and resize. Wheel input over
  browser content is retained as one bounded, saturating delta per renderer,
  encoded only when its discrete command slot is idle, and applied by the
  sandbox worker to one viewport-preserving layout shared by Draw IR paint and
  hit testing. Offscreen Draw IR nodes are culled before the protocol budget;
  document commit resets scroll, while resize reclamps it. Parent-owned cookies
  now enforce Secure, HttpOnly, SameSite, expiry, and schemeful-site
  partitioning through BrowserSession and redirect hops. Windows AppContainer
  and the signed macOS helper remain open.
- no current GC/RSS/soak or crash-containment evidence exists;
- existing browser interaction evidence can pass when its artifact is absent.

The persistent SimpleScript executor resets its compatibility runner to the new
document and event loop and clears callback bodies, timers, animation-frame
work, and document-scoped console entries on navigation and close. The inline
formatter now supports empty atomic inline-block baseline alignment through the
parent strut and resolved positive pixel margin edges. Non-empty/overflow
baselines and negative/percentage vertical-margin cases remain in the visible
unsupported ledger.

### Input, text, and Chromium hardening

- The renderer broker owns a bounded FIFO for same-document pointer, key, text,
  resize, scroll, and animation work. Navigation/network/history/Stop boundaries
  never enqueue input that could be replayed against another document.
- `DrawIrCommand.advance_widths` is the canonical resolved-font metric payload.
  Engine2D accepts computed-style CSV only as a legacy external-input fallback.
- Chromium capture and the live Electron shell run with renderer sandboxing,
  Node integration disabled, and context isolation enabled. Capture additionally
  denies popup and navigation away from its staged document.
- The parent profile owner sends at most 256 validated bookmarks through a
  typed snapshot message after renderer readiness and successful Favorite
  commits. The sandbox worker has no profile-file authority.
- The network broker owns transport cookies and removes all Set-Cookie response
  headers before renderer IPC. Script-visible cookie reads must use a separate
  origin-bound broker operation.
- Parsed form defaults are engine-private DOM state excluded from serialization;
  reset dispatches once before the shared form-owner subtree is restored.
- Process-lifetime default-font cache identity is the resolved finite built-in
  font path. Author-provided font faces are document/transient material.
- External images remain an open architecture lane: CSP `img-src`, HSTS and
  mixed-content decisions stay in the broker; decoded bounded pixels then enter
  layout and Draw IR through the existing image owner.
## External PNG image path (2026-07-29)

External `<img src>` follows the existing active-subresource broker path:
BrowserSession resolves the URL and enforces `img-src`, HSTS, mixed-content,
redirect, cookie, and cancellation policy. It decodes only bounded PNG input
into the existing `SimpleOsHostGpuImageResource`; `SBRF5` carries those
resources to the parent, and Engine2D converts them once to its existing
resolved Draw-IR image material. The resource key stays the authored `src`, so
layout needs no parallel URL resolver. Older frame versions remain decodable.

## CSS URL background path (2026-07-29)

CSS `url(...)` backgrounds reuse the bounded BrowserSession image owner. Inline
declarations retain their authored key, linked stylesheets rewrite to a
canonical resolved key, and both fetch through broker-owned CSP `img-src`,
HSTS, mixed-content, redirect, and cancellation policy. Layout emits one typed
background image behind element content with size, position, repeat, origin,
and clip geometry; rounded clips add canonical shape bounds and per-axis corner
radii to that command. Engine2D applies the rounded mask inside the existing
image sampling pass, so it allocates no second mask buffer. Across one
composition, accepted CSS-background sampling is charged against one
framebuffer-sized pixel-work budget; later commands fail closed when exhausted.
The canonical border overlay remains later in paint order.
The hosted worker filters composition-referenced resources before the additive
`SBRF5` retained-frame transfer, so unused stylesheet images do not inflate
each frame. Existing CSS animation invalidation and retained-frame timing remain
unchanged.

Multiple image layers and fixed/local background attachment remain fail-closed
until they have bounded lowering and exact-pixel evidence.

## Post-load browser boundary hardening (2026-07-29)

Post-load DOM reconciliation rediscovers inline and stylesheet background URLs
and routes each new `BrowserImageSource` through the same
`_start_image_source` owner used during document load. That preserves existing
CSP, HSTS, mixed-content, redirect, PNG, resource-budget, and
generation-cancellation boundaries; JavaScript and Simple Script gain no
parallel fetch or decoder path. A completed fetch updates retained images and
normal rendering invalidation without resetting document animation time.

The JS engines retain their bounded timer arrays but remove completed and
canceled entries in place. Due-task selection remains a bounded linear scan;
the old per-callback queue reconstruction and second retained list are gone.

Stop remains parent-owned. If a renderer command has been partially written,
the broker records `stop_after_write`, finishes that frame atomically, then
cancels navigation/network state and emits Stop within the refreshed deadline.
The worker drains complete messages already in its bounded decoder before
reading again, so a coalesced Stop cannot stall behind an empty read.

URL authority keeps bracketed IPv6 syntax, while socket/TLS receives the
validated bare literal from `_browser_transport_host`. The Linux final
renderer seccomp filter also denies `get_robust_list`, closing same-UID robust
futex-list disclosure without adding an app-local syscall facade.

Only focused host C containment/TLS evidence is currently executable. The
pure-Simple target remains blocked by the recorded compiler failure; no
bootstrap or Rust-seed result is production browser evidence.

## Shared-state and frame-work convergence (2026-07-29)

- `opacity: 0` suppresses the element and its entire descendant subtree before
  paint/Draw-IR emission. Fractional opacity remains incomplete until bounded group
  compositing can apply one alpha to a subtree without double blending.
- `BrowserProfileStore` remains the sole bookmark persistence owner. The host
  publishes one immutable snapshot plus monotonic revision to the primary
  renderer and keyed secondary registry; existing and newly admitted windows
  consume the newest revision when idle.
- Address editing is window-local. Escape restores the renderer's committed
  URL, or the entry's startup address before the first network commit; primary
  and secondary windows follow the same rule.
- Bracket removal for a validated IPv6 literal is owned by
  `hosted_browser_transport_host` and shared by in-process and sandbox-renderer
  HTTP/TLS paths. URL, origin, and history owners retain bracketed authority.
- Adjacent deferred resizes coalesce to the newest dimensions, and each
  animation frame serializes the HTML document once for both animation
  reconciliation and layout/paint.
- The bounded two-URL background profile stays on the canonical chain:
  BrowserSession resource policy → existing Style witness → ordered typed
  Draw-IR CSS-background commands → Engine2D. It introduces no WebIR, Draw-IR
  kind, renderer, or framebuffer.
- Visible material provenance retains identical ordered hashes but collects
  accepted witness lines and joins once, avoiding quadratic transient text on
  static and animated render paths.
