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
  paint/Draw-IR emission. **PROPOSED / UNIMPLEMENTED:** fractional opacity is a
  proven structural gap: flat
  commands or an adjacent helper batch cannot preserve the parent's exact paint
  slot while applying alpha once to the whole subtree. The composition must
  remain flat, with one `group` command referencing a child batch at that slot.
  Engine2D must recursively execute the referenced batch into transient
  premultiplied material, then source-over composite it once. Before allocating
  that material, admission must reject unknown, orphan, or duplicate batch IDs,
  multiply referenced children, cycles, and depth above the existing
  `HTML_MAX_TREE_DEPTH` of 512. The existing browser limits remain authoritative:
  at most 1,024 commands across every batch (groups included), therefore at most
  1,025 batches, at most 1,048,576 encoded payload bytes, and at most
  `viewport_pixels * 16` painted or transient pixels. Each clipped group-bounds
  pixel must be charged once to that same frame pixel counter; no second budget
  will be added. The root must remain the one opaque HTML batch. CSS lowering
  must keep `css_opacity_pct` separate from `filter_opacity_pct`; filter opacity
  must stay unsupported rather than being silently treated as subtree opacity.
  The nested pixel oracle must use a blue box at 50% inside a same-bounds,
  transparent/no-paint parent at 50%, over white: only blue has effective 25%
  alpha, yielding `0xFFBFBFFF`.
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

## Cascade provenance and parent-history authority (2026-07-30)

`overflow: clip` remains unimplemented. Flattening `@layer` blocks before rule
admission discards information required by the cascade, so a boolean added at
paint time would be a false implementation. The canonical path must preserve
declaration origin, importance, layer identity/order, specificity, and source
order from the parser through `Rules` to the single cascade owner. Only the
winning computed value may lower to clip semantics; it must remain distinct
from `hidden`, `auto`, and `scroll`.

History authority remains parent-owned. The current neighbor snapshot is not a
security boundary for History API mutation. The renderer protocol carries a
bounded complete ledger and current index under the random outer `SBR2`
capability. A private parent `HistoryAuthority` binds that capability to the
generation, root request, reply request, canonical origin, effective
CSP-ready/policy, and sandbox scripts decision.

### SBRHJ1 canonical parent-history protocol (2026-07-30)

Status: **IMPLEMENTED STATIC / EXECUTION HELD**.

`SBRHJ1` is the only renderer history-mutation representation. It carries the
complete bounded URL ledger, current index, resolved current URL, action, URL
argument tag, and matching SBR2 capability inside nested `SBRF9`. URL tags are exact:
`O` is omitted and has the literal wire sentinel `-`; `N` is JavaScript null
and has the same sentinel but resolves the WebIDL string `null`; `V` is an
explicit value and always carries canonical base64, including a zero-length
field for the explicit empty string. Thus omitted, null, and empty can never
alias. Resolving `V` with an empty field returns the complete committed URL,
including its query and fragment.

The renderer proposes only `P` push, `R` replace, or parent-commanded `T`
traversal. The parent validates the admitted private `HistoryAuthority`,
canonical same-origin resolution, complete ledger, and index. It derives the
sole legal transition off-side from its own 64-entry ledger, including forward
truncation and oldest-entry eviction, then performs one swap of URLs, CSP rows,
index, document URL, and chrome neighbors. Malformed, stale, forged, reordered,
non-neighbor, over-budget, cross-origin, CSP-unready, or sandbox-script-denied
proposals never mutate committed state. Renderer failure closes transport but
preserves established parent chrome/history; explicit close clears it.
Frames without `SBRHJ1` cannot mutate history; their neighbor strings are
ignored and parent chrome is derived only from the authoritative ledger.

Site-swap/restart and parent back/forward commands carry a bounded `SBRHJ1`
`N` snapshot in `SBN2` so a fresh renderer joins authority before navigation.
Back/forward reload a joined placeholder through the broker and replace the
parent-selected index; the renderer does not own a private durable ledger.

### Proposed cascade-owner root fix

Status: **PROPOSED / UNIMPLEMENTED**.

The current loss is concrete: `_css_scan_rules_simple` records `Layer`
wrappers, `_extract_css_vw_with_rule_limit` treats them as unconditional and
then drops their identity, and `css_declaration_priority_split` turns each
rule into parallel normal/important strings in `Rules`.
`compute_styles_with_material` sorts matching rules and concatenates those
strings for `apply_decls`; `presentational_attr_decls` and `nd.style_attr`
enter through separate calls. Finally `_apply_css_animations` calls
`apply_decls` after author-important declarations. No paint-only
`overflow_hidden` branch can recover that discarded ordering.

Retain the existing parser, selector matcher, and one cascade owner. Replace
only the lossy handoffs with these records:

```simple
enum CssCascadeOrigin:
    UserAgent
    User
    Author
    Animation
    Transition

class CssLayerIdentity:
    id: i32
    parent_id: i32
    name: text
    order: i32
    anonymous: bool
    implicit_outer_band_id: i32
    implicit_outer_order: i32

class CssRuleDeclaration:
    property: text
    specified_value: text
    origin: CssCascadeOrigin
    important: bool
    layer_id: i32       # -1 means unlayered
    layer_order: i32    # global order assigned by CssLayerRegistry
    layer_path: [i32]   # outermost to innermost identity
    source_order: i64   # per declaration, not per rule

class CssRule:
    group_parts: [[text]]
    group_specificities: [i32]
    declarations: [CssRuleDeclaration]

class CssCascadeDeclaration:
    property: text
    specified_value: text
    origin: CssCascadeOrigin
    important: bool
    layer_id: i32
    layer_order: i32
    layer_path: [i32]
    encapsulation_order: i32
    element_attached_style: bool
    specificity: i32
    source_order: i64

class CssCascadeBandRank:
    id: i32
    origin: CssCascadeOrigin
    important: bool
    encapsulation_order: i32
    layer_id: i32
    element_attached_style: bool
    precedence_rank: i32

class Rules:
    rules: [CssRule]
    layers: [CssLayerIdentity]
    bands: [CssCascadeBandRank]
```

`CssRuleScan` must retain the ordered layer path for every leaf rule and admit
ordered `@layer a, b;` statements. `CssLayerRegistry` assigns hierarchical
identity plus one stable global order: predeclarations fix first order,
reopened named layers reuse identity, nested names retain their parent path,
and every anonymous layer gets a new identity. Layer registration is
document-global and includes an `@media`/`@supports` layer only while every
enclosing condition applies. A false conditional layer has no identity or
order until it becomes applicable. A viewport or condition-truth change
rebuilds the complete applicable registry, compact band ranks, selector
buckets, and dependent computed styles before any node cascade runs.
Element-sensitive conditional layers cannot have node-local order; the bounded
profile rejects them conservatively until a document-global applicability
owner exists.

Every layer, including the top-level author origin, owns an implicit outer
sublayer for declarations written directly in that layer. That implicit
sublayer follows its named/anonymous child layers in layer order: its normal
declarations beat its child layers, while its important declarations lose to
important declarations in child layers. Thus unlayered rules are declarations
in the top-level implicit outer layer, not declarations with erased layer
identity.
Later normal layers win, while earlier important layers win.

A matched rule materializes `CssCascadeDeclaration` values using the maximum
specificity of its matching selector groups. Element-attached inline style is
an explicit rank above selector-matched declarations at the same
origin/importance, not a fabricated ID specificity. Presentational hints are
author-normal, unlayered, specificity zero, and ordered before author
stylesheets. Tag defaults are user-agent declarations. Encapsulation context
is part of the key because normal and important context order reverses; the
current light-DOM profile always uses context zero and rejects shadow-scoped
style input instead of claiming support. The `User` and `Transition` enum
values reserve the normative rank, but this profile admits neither user
stylesheets nor CSS transitions until those producers exist.

The cascade owner parses and validates declarations once, expands supported
shorthands before winner selection, and discards invalid declarations without
erasing an earlier valid candidate. It groups candidates by
origin/importance/encapsulation/layer and keeps the
element-attached/specificity/source-order winner for each property in each
occupied band. Each property retains that sparse, precedence-ordered
lower-candidate stack until defaulting completes; reducing to one global winner
early is forbidden. A single band traversal resolves all properties:
`revert-layer` removes the current layer's declarations and exposes the next
lower candidate in layer order. A normal declaration in the top-level implicit
outer layer therefore exposes the last explicit layer. A non-attached
important declaration in that implicit outer layer instead falls to the next
origin, because important explicit layers are higher, not lower, candidates.
Any element-attached `revert-layer` first removes only its attached tier; the
important case therefore exposes important style-rule candidates despite
reversed important-layer order before any origin rollback. `revert` removes
the current origin; author-origin `revert` also removes the animation origin,
as required by Cascade 5. `initial`, `inherit`, and `unset` then resolve
against property metadata plus the parent computed style. Thus rollback always
uses a real lower candidate and never reconstructs one from `Style`. These
CSS-wide values never reach `apply_decls`. Winning ordinary values go through
a renamed computed-value applier; it performs no cascade.

Custom-property tokens likewise remain attached to their declaration until
custom-property cascade selection; the current whole-sheet pre-substitution
must not erase their provenance. Animation samples enter the same owner as
`Animation` origin candidates, below every important declaration, and
transitions use the highest transition origin. Static winners remain cached;
an animation tick overlays only sampled properties.

The final representation keeps
`ComputedOverflowPair(x: CssOverflowMode, y: CssOverflowMode)` separate from
`UsedOverflowState(x: CssOverflowMode, y: CssOverflowMode, clip_box,
clip_margin_px, scroll_container, establishes_bfc)`;
`CssOverflowMode` is `{Visible, Hidden, Clip, Scroll, Auto}`.
Cross-axis computed-value rules run before layout: if either axis is neither
`Visible` nor `Clip`, `Visible` on the other axis computes to `Auto` and `Clip`
computes to `Hidden`. Computed style and used overflow state remain separate.
The root element's computed pair propagates to the viewport. For an HTML root
whose two computed axes are `Visible`, the first body child supplies the
viewport pair instead; the propagation source keeps its computed values but
uses `Visible` on the element box. At the viewport, used `Visible` becomes
`Auto` and used `Clip` becomes `Hidden`. On a replaced element, computed
`Hidden` remains observable as `Hidden` but its used value is `Clip`.

`Clip` and `Hidden` may share a paint clip primitive, but `Clip` creates no
scroll container and forbids programmatic scrolling; unlike the other
non-visible modes it does not itself establish a formatting context. Its
default overflow clip edge is the padding box with
`overflow-clip-margin: 0px`; margin expansion occurs before Draw IR emission.
The conformance gate separately covers root/body-to-viewport propagation,
replaced elements, float/BFC behavior, and programmatic scrolling. Until those
rows pass, the supported slice is light-DOM, non-root, non-replaced boxes and
must not claim full CSS Overflow 3. Draw IR receives used layout/paint state,
while CSSOM-facing state retains the computed pair.

Preprocessing is O(CSS bytes + rules + declarations). For one node, selector
matching plus cascade is O(candidate rules + matched declarations), worst-case
O(rules + declarations), with no candidate sort, declaration-string
concatenation, or declaration reparse. The applicable registry precomputes one
compact precedence rank per band. Selector buckets retain that rank order, so
the existing sorted-list merge streams matched candidates in band-rank order;
the first candidate for a band appends its ID to the node's occupied-band list.
Winner selection traverses only that list: O(occupied bands + matched
declarations), where occupied bands <= matched declarations. It never scans
the document's dense global layer/rank table per node. All occupied winner maps
together are O(matched declarations). Existing rule, declaration, selector,
and time budgets remain hard caps.

Invalidate the parsed rule/layer cache on stylesheet text or applicable-wrapper
changes; invalidate matched-node cascade state on class/id/attribute/inline or
presentational-hint changes. Selector invalidation follows dependency shape:
ancestor changes invalidate descendants for ancestor selectors and inherited
values; descendant changes invalidate candidate ancestors for `:has(...)`;
insert/remove/reorder invalidates the affected sibling/child cohort for
structural selectors plus dependent ancestors/descendants. Viewport changes
that change conditional truth rebuild applicable layer registration/order,
ranked selector buckets, and affected styles; a resize that changes no
condition retains them. A feature-profile change similarly reevaluates
`@supports`. Animation frames invalidate sampled properties and their existing
layout/paint classifications, not the static rule cache or whole tree.

This proposal implements only the repository's bounded light-DOM author
profile: user sheets, shadow-tree encapsulation, `@scope`, transitions, and the
overflow root/replaced boundary remain explicit RED rows. It follows Cascade 5
ordering for admitted inputs; it does not claim full Cascade 5.

References:

- [CSS Cascading and Inheritance Level 5 — cascade sorting order](https://www.w3.org/TR/css-cascade-5/#cascade-sorting)
- [CSS Cascading and Inheritance Level 5 — defaulting keywords](https://www.w3.org/TR/css-cascade-5/#defaulting-keywords)
- [CSS Overflow Level 3 — `overflow: clip`](https://www.w3.org/TR/css-overflow-3/#valdef-overflow-clip)

<!-- codex-architecture -->
## Bookmark title witness boundary (IMPLEMENTED STATIC / EXECUTION HELD)

Before this implementation, both hosted production paths committed
`toggle_bookmark(url, url)`, discarding the bounded
`BrowserSession.current_title`. Both paths now call the single profile-owned
`hosted_browser_parent_toggle_bookmark` transaction; the SSpec invokes that
same production function after the real `favorite-parent` action.

`BrowserProfileStore` owns one SQLite boundary for the current-row read,
insert/delete, and ordered canonical snapshot query. It commits only after the
snapshot query succeeds and returns the snapshot as part of the committed
mutation result. Any mutation, snapshot-read, or commit error rolls back; the
parent may update bookmark revision and UI state only from that committed
result. The in-process host follows the same contract and restores its exact
pre-release browser value on failure.

The existing frame contract is the only new authority needed. `SBRF8` extends
`SBRF7` with one base64 document-title payload and encoded-length field:

`SBRF8 reply cpu-count cpu-digest solid-count solid-digest next-ms diagnostics-len current-url-len back-url-len forward-url-len title-len image-count image-checksum image-len composition-revision`

Payload order is diagnostics, current URL, back URL, forward URL, title, image
records, then Draw IR. The decoded UTF-8 title is at most 512 bytes and contains
no NUL. Before base64 decode or decoded-title allocation, admission requires a
canonical decimal `title-len` in `0..684` and computes every payload segment end
with checked addition. Only after those ordered ends locate a fully contained
title slice does it scan base64 alphabet/padding without allocation and derive
a decoded size at most 512. The encoded title bytes plus derived decoded bytes
are charged against the existing 1 MiB frame/Draw-IR payload budget before
allocation. Decode is accepted only when re-encoding produces the exact
original base64 text. Truncation, trailing overlap, integer overflow, or budget
exhaustion rejects the frame.

The envelope generation, frame reply ID, and existing current-URL field form
one title witness; the parent may retain it only after the reply and generation
pass existing admission and that current URL equals the parent-committed
canonical URL. A stale generation, stale reply, or URL mismatch cannot change
title state.

An honest worker maps an empty, NUL-containing, or over-512-byte page title to
an absent title witness so hostile content cannot make every frame fail. A
malformed nonempty `SBRF8` title remains a protocol violation. `SBRF2..SBRF7`
stay render-decodable with `document_title_present = false`; they never inherit
a cached title. Production Favorite may still use the canonical-URL fallback,
so compatibility does not create stale-title authority.

Bookmark title handling remains in the existing BrowserSession/profile
capsule—no new service or storage schema. The shared
`hosted_browser_title_is_valid` validator admits a trimmed, nonempty title only
when its UTF-8 size is at most 512 bytes; otherwise the stored title is the
existing empty sentinel. One shared display helper uses
that stored title or the separately bounded canonical URL. The URL fallback is
derived, not copied into the 512-byte title column or snapshot field. Profile
schema version 1 therefore remains valid, old URL-as-title rows remain readable,
and an invalid title row can fall back without granting its text authority.

The parent clears ephemeral title state at navigation replacement, site-swap
generation replacement, renderer failure, and close. A replacement renderer
must produce a newly admitted witness; title state is never copied across the
generation boundary. Persisted bookmarks remain profile-owned and survive
window/host restart. The in-process path calls the same validator with
`current_title` and must not overwrite the accepted title with `(url, url)`.

Static source, hostile protocol fixtures, generated manuals, and profile
restart coverage exist. The hostile fixtures include a syntactically valid
forged SBRF8 whose decoded title is 513 bytes, and the profile fixture injects
a post-mutation snapshot-read error and proves row/title/revision/UI and restart
parity remain unchanged. They do not establish an executable PASS; production
acceptance remains held for an admitted current pure-Simple full CLI and hosted
artifact run.

<!-- codex-architecture -->
## Renderer command capability boundary (PROPOSED / UNIMPLEMENTED / RED)

Numeric generation and request IDs order renderer traffic, but they do not
prove that a reply was produced after its host command was issued. During
startup the decoder can retain a second message after `ready`; request ID `2`
is predictable, so a syntactically valid frame naming reply `2` can later pass
the current numeric check after `init` is written. The same causal gap applies
to later command/fetch/frame chains. This section defines a defensive protocol
repair only; current production remains RED.

The host creates one opaque `BrowserRendererCommandCapability` for every
host-to-worker wire, including every `network_response`, rather than reusing a
root-command token. It is exactly 16 bytes from the hosted platform CSPRNG,
encoded as 32 lowercase hexadecimal ASCII bytes. Entropy acquisition has an
explicit success result; short reads, unavailable entropy, all-zero test
sentinels, or any noncanonical encoding fail renderer startup/command
admission. The token is never derived from generation, PID, time, or request
counters and is never logged. The runtime facade, not browser policy code,
owns Linux `getrandom`, macOS `SecRandomCopyBytes`, and Windows
`BCryptGenRandom`.

The production wire moves from numeric-only `SBR1` to fail-closed `SBR2`.
Its bounded header carries only a canonical capability length (`0` for
`ready`, otherwise `32`); the capability bytes are the final trailer after the
declared payload. A decoder does not release a message until the complete
trailer is present. Consequently a worker cannot learn the token until all
payload bytes for that host wire precede it in the pipe.

The trailer is charged inside, not added above, the existing 1 MiB payload
budget: checked addition requires
`payload_bytes + capability_bytes <= BROWSER_RENDERER_MAX_PAYLOAD_BYTES`.
The streaming decoder retains the existing total cap of
`BROWSER_RENDERER_MAX_HEADER_BYTES +
BROWSER_RENDERER_MAX_PAYLOAD_BYTES +
BROWSER_RENDERER_MAX_READ_CHUNK_BYTES`; SBR2 does not increase it. Generation,
root-command ID, wire ID, and reply ID use canonical unsigned-decimal text in
`1..BROWSER_RENDERER_MAX_SEQUENCE_ID`, where the maximum is
`9223372036854775806`. Zero is admitted only for ready's root ID. Every
increment uses checked addition; exhaustion fails closed before installing a
wire or advancing registry generation. Leading signs, leading zeroes,
`9223372036854775807`, and textual max-plus-one overflow reject.

The root command establishes a stable
`(generation, root_command_request_id)` chain. Each host wire carries a fresh
tail capability; the next worker `fetch_request`, `test_hang_ready`, or
terminal `frame` echoes that one token exactly once. A `network_response`
revision additionally names the originating renderer fetch wire ID and carries
a new tail capability. The worker validates that immediate reply ID before
committing the response, then may echo the new token in its next fetch/frame.
Fetch and frame payload revisions retain their existing
`reply_to_request_id`. Thus admission requires all four facts:

1. message generation equals the live renderer generation;
2. root command request ID equals the host's issued root request ID;
3. capability exactly equals the host's one live, unconsumed 32-byte hop
   capability; and
4. reply ID exactly equals the latest completely written host wire ID.

Capability validation precedes request policy, cookie mutation, network-job
creation, frame decode, history/title updates, retained-image replacement, and
renderer state transition. A missing, malformed, retired, or mismatched token
returns `unissued-renderer-reply` and enters the existing fail/close cleanup
path. Generation rejection remains earlier and reports `stale-generation`.
No comparison accepts prefixes or case variants.

The host consumes the live hop capability immediately after one bound worker
message passes correlation, before broker dispatch or frame decode. A fetch
therefore retires its token before network work starts; the later
`network_response` installs a fresh token only when its complete wire becomes
pending. A terminal frame consumes its token before state transition.
Cancellation, stop replacement, timeout, decoder violation, network failure,
renderer failure, site swap, `close`, and registry teardown retire any live
token. Only failure, close, site swap, and registry teardown clear retained
display resources; ordinary cancellation/stop preserves the last admitted
frame. Deferred commands receive a capability only at activation. A
replacement renderer inherits neither token nor generation.

The host separates staged from issued authority. Encoding/installing a pending
wire fills
`staged_generation`, `staged_root_request_id`, `staged_host_wire_request_id`,
and `staged_hop_capability`; all issued fields remain empty. Only
`_flush_pending_wire_once`, after checked subtraction proves pending remaining
bytes reached exactly zero, atomically moves that tuple to the corresponding
`issued_*` fields and clears `staged_*`. Admission consults only `issued_*`.
Neither partial write progress nor the staged token can authorize a renderer
message.

Legacy `SBR1`, legacy fetch/frame schemas without the root command ID, and a
legacy `network_response` are rejected in the production broker and worker.
There is no downgrade flag, environment escape hatch, or legacy decoder
surface.

As defense in depth, startup accepts `ready` only when its payload and
capability trailer are empty, its request ID is `1`, and the decoder has no
retained bytes. This check catches same-read protocol overrun, but it is not
the causal boundary: only the not-yet-disclosed tail capability proves that a
reply followed a completely delivered host wire.

The exact owners stay narrow: `src/lib/common/web/browser_renderer_protocol.spl`
owns SBR2 framing and canonical validation;
`src/os/hosted/hosted_browser_renderer_process.spl` owns token creation,
staging, issuance, admission, broker ordering, and retirement; and
`src/os/hosted/hosted_browser_renderer_worker.spl` owns complete-wire decode,
one-use echo, and network-response sequencing. The parent reuses only the
existing `src/lib/nogc_sync_mut/io/crypto_sffi.spl` `random_hex(16)` facade;
the common codec and worker do not own or import the private parent creator and
cannot install or consume parent `issued_*` state. Arbitrary random hexadecimal
text grants no authority.

<!-- codex-architecture -->
### Hosted-parent command-token creator (PROPOSED / UNIMPLEMENTED / RED)

The zero-argument
`browser_renderer_command_capability_new() -> Result<BrowserRendererCommandCapability, text>`
is a private function in
`src/os/hosted/hosted_browser_renderer_process.spl`. It calls the existing
`crypto_sffi.random_hex(16)` facade once for each activated host wire, then
validates the result with the common protocol
`browser_renderer_command_capability_valid`. Entropy failure, NIL, wrong
length, nonhex, uppercase, or all-zero output maps to
`renderer-command-entropy-unavailable` before any pending-wire, deadline,
request-ID, staged-authority, or broker state changes. There is no public
capability-minting API, raw runtime import, alternate RNG, deterministic
fallback, production fault switch, or page/script access path.

The security boundary is causal rather than nominal. Any trusted hosted module
can format 32 hexadecimal bytes, but only `HostedBrowserRendererProcess` owns
the issued tuple and installs it after the complete wire is written. Renderer
authority therefore requires the live generation, root ID, immediate wire ID,
and exact unconsumed capability. The parent consumes that tuple before broker
or frame authority; the worker only echoes the final trailer it learned from a
complete host wire. Deterministic evidence drives the private parent
creator/conversion error path and proves all parent authority fields remain
unchanged. Only parent activation state evidence is admissible.

The production switch is one atomic common-codec + parent + worker migration.
It promotes SBR2 for every command, `network_response`, fetch, and frame
direction, installs every retirement path, and rejects SBR1 and legacy nested
schemas on both sides. Partial direction changes, legacy negotiation,
downgrade flags, and mixed SBR1/SBR2 deployments are forbidden.

## Generation-qualified DOM identity and index

<!-- codex-design -->

Status: **INTEGRATED STATIC CANDIDATE / TARGET EXECUTION HELD**.

Design-audit status: **COMBINED OWNERS/APIS PRESENT; RUNTIME/NFR EVIDENCE HELD**.

The current author-ID-or-`node_id` strings and recursive
`be_dom_find_path_to_id` calls are not a production identity model. They can
retarget stale events after a reparse, make external form/radio association
quadratic, and let label, listener, UI-access, and hosted pointer paths
disagree. The replacement is one semantic DOM-owned index, not separate label,
radio, or listener identity registries.

The import-free
`src/lib/gc_async_mut/gpu/browser_engine/dom_limits.spl` owns only
`HTML_MAX_TREE_DEPTH` and `HTML_MAX_NODES`. The parser and identity index
import those constants; the limits module imports neither DOM nor web/session
code. This removes the private-constant and GPU-to-web dependency without
creating another policy owner.

`src/lib/gc_async_mut/gpu/browser_engine/dom_identity_index.spl` exclusively
owns:

- `DomDocumentGeneration`: a checked positive `i64` document incarnation;
- `DomNodeRoute`: `{ generation: DomDocumentGeneration, node_id: i64 }`;
- `DomRadioGroupKey`: the generation-qualified form-owner route (or no owner)
  plus the nonempty radio name; and
- `DomIdentityIndex`: one immutable index for the committed generation.

Each route entry stores only its parent route and child ordinal in the existing
DOM tree; it does not copy a full root-to-node path or own another node tree.
The index also stores first-preorder nonempty author ID to route,
form-associated node to form-owner route, label route to control route, radio
route to group and group to preorder members. Parent entries reconstruct both
structural and event paths in O(depth). Duplicate author IDs keep the first
preorder route and increment a counter; a later node never silently wins.
JavaScript `getElementById`, explicit label `for`, and external `form` use that
same winner rule. Numeric node IDs are unique and never reused within one
generation. Without `for`, the first labelable descendant wins.

`dom_identity_index_build(root, generation)` performs two bounded preorder
passes. Pass one assigns routes, parent identity/child ordinal entries, first
author IDs, and unresolved associations. Pass two resolves form/label
references and radio groups from recorded rows. Neither pass invokes a tree
search. Duplicate `node_id`, checked-generation exhaustion, excessive depth,
or `HTML_MAX_NODES` rejects before publication. Expected
O(1) index queries cover route membership, author ID, form owner, label
control, and radio key. Structural-path reconstruction, route-to-node, and
event-path queries are O(depth), bounded by admitted depth; radio enumeration
is O(group size).

Layout hit keys are renderer output, not DOM identity.
`DomIdentityIndex.route_for_layout_target_key` accepts only the existing
canonical `id:` and `path:` forms, resolves `id:` through the first-author-ID
map and `path:` through a body-rooted layout relation, and returns a
`DomNodeRoute`. Pass one records exactly
`(layout_parent_route, layout_element_ordinal) -> route`. The root is the
first preorder `body`; `path:` names that route. An ordinal counts only direct
children accepted by the existing layout-element predicate, so text plus
`style`, `script`, `title`, `head`, `meta`, `link`, and `base` neither receive
a relation entry nor increment it. `BrowserSession.route_for_layout_target_key`
additionally requires the caller's captured `DomDocumentGeneration`; mismatch
returns `stale_target` before parsing or consulting the current index.

`BrowserSession` owns exactly one current
`(DomDocumentGeneration, DomIdentityIndex)` pair. Navigation/document/root
replacement and every committed mutation batch that changes membership or an
identity/association input (`id`, `form`, `for`, radio `name`/`type`, or
labelable structure) build the candidate index first, advance generation, and
atomically publish DOM plus index. One batch means one build and one
generation. Value, style, focus, and text mutations that preserve those inputs
reuse the current pair.

The integrated session boundary exposes the pair through
`document_generation()` and `current_dom_identity_index()`. Renderer input
enters through `route_for_layout_target_key`; reverse rendering projection is
`layout_target_key_for_route`, while page-visible author projection is
`author_id_for_route`. `publish_dom_snapshot` is the one staged commit boundary
for DOM, index, runtime bridge, and SimpleScript state. The focused
SSpec/manual exercises these names statically without promoting runtime or NFR
status.

Dispatch freezes its event path as `DomNodeRoute` values. After each handler it
first compares the captured and published generations. A mismatch never looks
the old route up in the new index: the current handler unwinds, then remaining
page callbacks, follow-on events, and default actions abort as `stale_target`.
Only when generation is unchanged may focus, edit, label, radio, form, or
default-action work re-resolve its route in that same index. Removal and
identity mutation therefore cannot retarget by author ID or reused numeric ID.
Dispatch may pin the old immutable index only until unwind; escaped bridge
objects retain routes, never the index.

`BeDomEvent` remains the page-visible payload, but its stored text
`target_id`, `current_target_id`, and `related_target_id` fields and
text-target constructor parameters are removed from production dispatch.
Author-facing IDs are computed on demand as projections after resolving a
typed route in the captured index. The production dispatch frame owns typed
`target_route`,
`current_target_route`, `related_target_route`, and frozen
`[DomNodeRoute]` propagation state. The legacy text
`BeDomEventDispatch.target_route_id` and `current_target_route_ids` fields are
removed in the atomic migration.

The outermost dispatch owns one document-wide budget shared with reentrant
dispatch: at most the existing 4,096 live callable listeners, 4,096 examined
listeners/actions, and `HTML_MAX_TREE_DEPTH` event-path entries. Nested label
activation and synthetic events consume the same budget. Label forwarding is
suppressed for an interactive descendant, and a
`(generation, label route, control route)` reentrancy key prevents recursive
forwarding. Exhaustion stops page callbacks/default actions before a partial
form submission.

Label activation captures its associated control route before author handlers.
Canceling the label prevents forwarding; canceling the synthetic control click
rolls back its pre-activation checkbox/radio state. The observable sibling
order is `label, control`; a control nested in its label produces
`label, control, label` as the control click bubbles. Hidden inputs are not
labelable and disabled controls receive no synthetic click.

Radio identity is `(generation, optional form-owner route, nonempty name)`;
the no-owner case is explicit and never represented by the document root.
Rollback stores the prior checked route, not author ID. Form serialization
uses the admitted post-event group once. Callable and SimpleScript listeners
bind routes, freeze the propagation path once, and do not search the DOM per
listener.

Script mutation uses the same candidate transaction as parser/navigation
replacement. `BrowserRuntimeState`, `SimpleScriptExecutor`, `ScriptHost`,
`JsDomBridge`, and load-time script wiring stage candidate DOM, runner roots,
route-bound listeners/callbacks, and identity inputs;
only `BrowserSession` builds the candidate index and publishes
`(DOM, generation, index, script state)` atomically. Failed index construction
or any script/bridge staging failure restores the prior `BrowserRuntimeState`,
`ScriptHost`/`SimpleScriptExecutor` roots, runner roots, listeners, and
callbacks. Handler-triggered replacement discards every old-generation
candidate component. No script owner or `browser_session_loading.spl`
`bind_dom` call publishes a private root/listener set ahead of the session
pair.

All consumers carry `DomNodeRoute`, never author ID or bare `node_id`:

- `browser_session.spl` owns generation/index, pending-Space, selection, focus,
  and runtime-bridge route state;
- `browser_session_runtime.spl` owns atomic publication, dispatch frames,
  handler re-resolution, blur/change/focusout, and default actions;
- `script_host.spl`, `simple_script.spl`, `event_api.spl`, and
  `js/dom_bridge.spl` stage typed route/listener/script mutations and never
  retain an independently current DOM;
- `browser_session_loading.spl` joins that transaction and retires direct
  `bind_dom` publication;
- `dom_accessors.spl` becomes an index-query shim and retires recursive
  identity/form/radio/event-path scans;
- `browser_session_form.spl` accepts qualified form and submitter routes;
- `browser_session_ui_access.spl` serializes qualified targets and rejects
  stale snapshots;
- `hosted_web_content_session.spl` and
  `hosted_browser_renderer_worker.spl` retain qualified press/focus routes and
  clear them on mismatch, replacement, cancel, or close; and
- JavaScript/SimpleScript bridge objects and listeners store routes; host
  mutation first requires the same generation, then resolves in that index.

Replacement and close stage clears for pending Space, selection, hosted
press/release, UI-access targets, and listener/action queues. Those clears
publish with the candidate DOM/index/script state at one assignment boundary;
only after host cleanup unwinds is the retired index released. Production
accepts no NUL-prefixed legacy route after migration.

The one-tree integration deletes, rather than deprecates, the production
legacy census: `be_dom_event_identity` and its `node:<node_id>` fallback,
`be_dom_route_identity`, `be_dom_route_node_id`,
`_be_dom_find_path_to_identity`, `be_dom_find_path_to_id`,
`_be_dom_implicit_submit_blocker_count`,
`be_dom_form_allows_direct_implicit_submit`, every NUL
`route-node:` parser/branch, `_script_host_apply_event_action_to_id`,
`script_host_apply_action_to_id`, text
`BeDomEvent.target_id`/`current_target_id`/`related_target_id`,
`BeDomEventDispatch.target_route_id`/`current_target_route_ids`,
`event_api.event_create(..., target_id)`, `JsDomListener.node_id`, hosted
`pressed_target_id`/`last_target_id`, and `_browser_dom_target`. Author IDs
remain content attributes and page-visible on-demand projections, but an
absent author ID projects empty text rather than `node:<node_id>`. Production
`getElementById` and author association use the index's O(1)
`route_for_author_id`; generic recursive selector compatibility may remain
only outside routing authority. Recursive selector/text/layout walks that are not identity,
association, event-path, or dispatch lookup remain outside this deletion.

At `N` and `2N` routable elements, build visits/allocations must scale within
10%, elapsed `2N/N <= 2.2`, and queries must report no recursive/full-tree
searches; structural and event paths report O(depth) work. A 10,000
replacement/dispatch cycle must release all retired indexes, remain within
existing input-to-paint/RSS limits, and return retained bytes/RSS within 10%
of the post-warmup baseline. These are future receipts; this design changes no
requirement status.

## Fixed-position layout, stacking, and hit ownership (2026-07-31)

<!-- codex-design -->

Rejected candidate `c3cb635fca2` is not an implementation base. It adds a
second whole-document fixed-layout pass and leaves formatting-context dispatch,
paint order, and hit order as separate authorities. Recovery keeps the existing
Web layout -> `DrawIrComposition` -> Engine2D route and freezes these owners:

- `simple_web_is_out_of_flow_positioned(style)` is the one classification used
  by block, flex, grid, and table measurement. Those formatters only exclude
  such children from normal-flow consumption; they never lay them out. When an
  auto/auto axis needs a static fallback, the formatter records that candidate
  origin without advancing tracks, rows, lines, or sibling flow.
- `layout_with_style` wraps `_layout_formatting_context`, then invokes
  `layout_out_of_flow_positioned_children` exactly once for the parent's direct
  absolute/fixed children. Recursive child layout repeats that wrapper rule, so
  no formatting context owns a private positioned-child branch or a document
  rescan.
- `PositionedContainingBlock` carries padding-box origin/size, fixed clip root,
  and viewport-fixed state. `_fixed_containing_block` selects the nearest
  admitted non-`none` transform ancestor, otherwise `(0, 0, viewport width,
  viewport height)`. A transformed containing block is its padding box:
  border-box origin plus border widths, with border widths removed from its
  size. Positioned offsets and percentages resolve against that box.
- Computed style retains mutually exclusive `position_fixed`, the independent
  `transform_containing_block` bit, and `z_index_auto`. Four
  `CssCoordinateValue` insets preserve `auto`, pixels, and percentages until
  containing-block used-value resolution; `right`/`bottom` are not integer
  sentinels and percentages are not prematurely converted. An independent
  `Transform2DSpec` resolves, after the untransformed border box exists, to one
  `UsedTransform2D` affine matrix. Transform parsing never writes `left`/`top`,
  width/height, or `position_relative`, and explicit `z-index: 0` never
  collapses into `auto`.

Viewport-fixed boxes and their ordinary descendants ignore root scroll, do not
extend scrollable content, and begin with the viewport clip rather than an
ordinary ancestor overflow clip. Fixed boxes whose containing block is a
transform move with that ancestor and use its normal ancestor clip chain.
Overflow clips inside either fixed subtree continue to intersect normally.
The same resolved clip cache gates visibility, Draw IR lowering, raster
evidence, and hit eligibility.

Fixed containing-block search begins at the node's parent. A node's own
transform therefore applies only after its inset layout and cannot make the
node its own containing block; that transform may establish the padding-box
containing block for fixed descendants. The resolved affine matrix is the sole
visual transform consumed by Draw IR geometry, clipping, and hit traversal.
Hit testing uses its inverse rather than a separately shifted layout box.

`simple_web_stacking_paint_order(nodes, styles) -> [i32]`, in the neutral
renderer core, is the sole stacking result. It keeps nested contexts atomic and
orders explicit negative contexts by ascending z/source order, then normal-flow
nodes, then one stable tree-order zero phase interleaving positioned `auto` and
explicit-zero contexts without collapsing their distinct context ownership,
then positive contexts by ascending z/source order. An ordinary static
non-flex/grid box ignores an authored z-index. Fixed boxes establish a context
even at `auto`; other positioned `auto` boxes remain in their parent context.
Draw IR traverses this array forward. Hit testing
traverses the identical array in reverse and accepts the first visible,
clipped, pointer-eligible owner; it performs no independent z-index comparison.

No private WebIR, Draw IR, hit-order, transform, clip, or font path is admitted
by this design. Implementation and runtime evidence remain RED.
