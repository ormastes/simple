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

State:

- source/document revision and viewport;
- canonical nodes, rule buckets, child index, computed styles, layout;
- current `DrawIrComposition`;
- one event loop, animation controller, render state, and monotonic clock;
- dirty stage and parse/style/layout/paint counters/timings.

Invalidation:

| Change | Work |
|---|---|
| navigation/source | parse, CSS, style, layout, paint |
| structural DOM | child index, style, layout, paint |
| class/id/style/pseudo | style, then layout only for geometry/font metrics |
| color/opacity/transform | paint |
| viewport/media | style, layout, paint |
| scroll | paint |
| unchanged frame | reuse composition/pixels |

Initial production scope may repaint the full dirty frame. Partial damage is
deferred until profiling proves it necessary.

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
  now rejects every document request unless it
  exactly consumes one parent-issued canonical URL/method/header/body permit,
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
  document commit resets scroll, while resize reclamps it. Parent-owned cookie
  state remains incomplete. Windows
  AppContainer and the signed macOS helper also remain open.
- no current GC/RSS/soak or crash-containment evidence exists;
- existing browser interaction evidence can pass when its artifact is absent.
