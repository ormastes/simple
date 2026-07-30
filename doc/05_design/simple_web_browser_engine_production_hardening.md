<!-- codex-design -->
# Simple Web Browser Engine Production Hardening — Detail Design

## Scope

Implements selected Feature B/NFR B without adding a second browser, DOM,
event, font, history, or rendering architecture.

## Stable interfaces

### Existing interfaces retained

- `BrowserSession.begin_network_navigation`
- `BrowserSession.stop_loading`
- `BrowserSession.reload`
- `BrowserSession.go_back`
- `BrowserSession.go_forward`
- `BrowserSession.go_home`
- `BrowserSession.ui_access_snapshot`
- `BrowserSession.ui_access_act`
- `DrawIrComposition`
- `Engine2dCompositorBackend`

### Minimal additions

```text
enum JsRuntimeProfile
  Browser
  Node

class BrowserRendererProcess
  pid
  generation
  receive_endpoint
  send_endpoint
  restart_window

class BrowserDomDispatchResult
  handled
  default_prevented
  target_id
  trace
  navigation

class SimpleWebRenderSession
  document_revision
  viewport
  dirty_stage
  canonical semantic/layout state
  DrawIrComposition
  clock/event/animation state
  counters
```

No factory or single-implementation trait is added.

## Navigation state machine

States:

- `committed`: current document remains visible;
- `pending`: a navigation generation owns document/resource work;
- `stopped`: pending generation canceled; late replies rejected;
- `failed`: last committed document remains visible with typed status;
- `crashed`: renderer generation invalidated; chrome/profile preserved.

Transitions:

```text
submit/link/reload/history -> pending(generation + 1)
pending + matching response -> atomic commit
pending + stop             -> stopped, cancel all generation work
pending + error            -> failed, no history commit
renderer violation/crash   -> crashed, discard renderer generation
restart                    -> new renderer generation, internal recovery page
```

Every request/reply includes renderer and navigation generation plus request
ID. Duplicate, unknown, or late replies are rejected.

## Browser profile persistence

- Default path: the platform data directory under
  `simple/browser/profile.sqlite3`.
- Schema version 1 stores at most 256 ordered bookmarks and 1024 HSTS hosts.
- Bookmark URLs and HSTS hosts are validated before save and again when loaded
  into BrowserSession.
- HSTS persists wall-clock receipt/expiry only; BrowserSession converts the
  remaining lifetime to its monotonic clock.
- Browser-window close saves before destruction. A failed save keeps the
  window open; WM shutdown reports failure after closing renderer resources.

## URL and resource decisions

1. Parse with canonical `Url`; reject control characters and credentials.
2. Resolve relative URL against committed document.
3. Derive initiator `Origin` in broker state.
4. Apply scheme and secure-context policy.
5. Apply CSP destination policy.
6. Fetch with bounded redirects, body, decompression, and timeout.
7. Validate TLS and HSTS before exposing bytes.
8. Combine repeated CORS fields, reject duplicate allow-origin grants, then
   apply response filtering and MIME policy.
9. Update broker cookie jar.
10. Send only permitted response fields to renderer.

Hosted TLS applies one five-second budget across bounded DNS, resolved numeric
connect attempts, the authenticated handshake, writes, and reads. The original
hostname remains the SNI/service identity. Linux/FreeBSD use the optional
OpenSSL provider with platform trust, TLS 1.2+, a 256-handle cap, per-handle
locking, and SIGPIPE suppression. A TLS read error or timeout invalidates the
runtime handle; H1 rejects the response instead of parsing or committing
partial bytes as an EOF-framed body. H1 frees provider-owned read/protocol/DNS
strings immediately after copying or validation.

`file:` content is never read by BrowserSession. A user-selected exact root may
be read by the broker through an explicit capability; page-originated file
access remains denied.

## Cookie/storage model

Cookie key: `(partition_site, domain, host_only, path, name)`.

Request matching checks:

- unexpired;
- secure transport for `Secure`;
- host-only equality or validated Domain suffix;
- path boundary;
- SameSite request context;
- selected credentials mode.

The broker attaches request cookies and receives `Set-Cookie`. Renderer
`document.cookie` sees and mutates only non-HttpOnly cookies allowed for its
committed origin.

Storage is partitioned by canonical origin. Navigation swaps the renderer's
visible storage proxy without exposing other partitions.

## JavaScript and Simple Script

- BrowserSession constructs `JsRuntimeProfile.Browser`.
- Node consumers explicitly construct `JsRuntimeProfile.Node`.
- Browser profile contains selected DOM, events, timers, rAF, fetch, URL,
  location, navigator, storage, console, and form bindings.
- Unsupported syntax/API returns a typed script error.
- Exact-source compatibility fast paths cannot satisfy conformance claims and
  are removed or restricted to named fixtures.
- Production Simple Script runs inside the same browser capability/event/DOM
  boundary; it does not write source to `/tmp` or launch `bin/simple`.

## DOM and event algorithm

Canonical tree construction assigns document-local node IDs.

Event dispatch:

1. hit test or semantic action selects a current node ID;
2. build ancestor path from current DOM;
3. invoke capture listeners root to parent;
4. invoke target capture then target bubble listeners;
5. if bubbling, invoke parent to root listeners;
6. record exact trace and cancellation;
7. if not canceled, run one default action;
8. apply mutations and invalidation;
9. render/present once.

Detached or previous-document IDs return `stale_target`.

Default actions:

- anchor click/Enter: navigate;
- input typing: mutate value and emit `beforeinput`/`input`;
- blur/commit: emit `change` when value changed;
- button: click;
- submit button: cancelable form submit then serialize/navigation;
- checkbox/radio: toggle/select then input/change;
- Tab/Shift+Tab: focus traversal;
- Enter/Space: control-specific activation.

Wheel input over browser content is coalesced into one bounded signed delta
while the renderer is busy. The worker applies it to document-owned scroll
state, clamps against the laid-out content bottom, and uses the same shifted
layout for paint and hit testing. A successful document commit resets scroll;
failed or blocked navigation keeps the current document position.

## Chrome/UI access

Stable chrome IDs:

`back`, `forward`, `stop`, `reload`, `home`, `favorite`, `address`, `title`.

Address behavior:

- `set_value` edits `address_draft`;
- `submit` normalizes and navigates;
- pressing any non-address chrome control ends address editing before its
  action, allowing the next committed frame to refresh the visible URL;
- invalid input returns `invalid_url` without state mutation.

Favorite click toggles current committed URL. Snapshot revision increments and
`UiAccessEvent` appends after accepted state changes. DOM nodes use
`dom-<node_id>` IDs and expose role/name/value/enabled/selected/focused,
relationships, and actions.

## Render algorithm

`SimpleWebRenderSession` retains semantic stages and begins at the current
dirty stage. Each stage increments count and elapsed time.

```text
parse -> CSS/rule index -> computed style -> layout -> paint/Draw IR -> submit
```

Stage invalidation follows the table in the architecture document. On an
unchanged frame, all stage counters remain unchanged and the current
composition/pixels are reused.

One monotonic `now_us` drives microtasks, timers, rAF, CSS animation, and the
rendering opportunity. Due timers run before the one rAF batch. Script and
animation mutations merge into a single invalidation before paint. rAF receives
the current rendering-opportunity time even when its deadline was missed.
Script-created elements and class/animation declaration restarts record a
per-node epoch relative to that document clock. Layout reconciles computed
animation identities only after DOM/style/viewport invalidation, passes the
bounded instance sidecar to sampling and hit testing, freezes paused elapsed
time, and includes each instance epoch in finite animation-end scheduling.
Removed nodes are swept; author-facing DOM/HTML serialization remains unchanged.
The layout result also reports the first actual animation change: positive
delays sleep until their start boundary, then active animations use the normal
frame cadence instead of polling unchanged pre-delay frames at 60 Hz.

Scrolling preserves the real viewport dimensions so viewport-relative CSS
and flex layout do not change with scroll depth. Paint culls boxes wholly
outside that viewport before Draw IR submission.

### Exact retained-render contract

The TDD gate lands before each implementation slice. The first focused
worker/session SSpecs fail on real counter expectations for unchanged advance
and close reclamation. Later slices add real expectations for navigation, DOM
mutation, stylesheet/resource commit, viewport resize, active animation,
scroll, caret overlay, and soak replacement before implementing each row.
Source-text presence checks do not satisfy those behavior gates.

```text
BrowserRenderRevisions
  document_revision  # existing ui_access_revision, repaired
  style_revision
  resource_revision

BrowserRenderSnapshot
  revisions
  document_html?     # present only when document/style changed

SimpleWebRenderCounters
  serialize_count parse_count css_count style_count layout_count paint_count
  reuse_count composition_revision
  serialize_us parse_us css_us style_us layout_us paint_us
  retained_node_count retained_style_count retained_box_count
  retained_command_count

SimpleWebRenderSession
  viewport_revision composition_revision
  prior BrowserRenderRevisions + viewport/scroll/overlay/time keys
  one existing private semantic/layout stage set + one DrawIrComposition
```

Current authoritative mutation owners to repair (line numbers are from the
2026-07-29 audit and symbol names remain authoritative after edits):

| Owner | Current location | Revision |
|---|---|---|
| DOM replacement | `browser_session_runtime.spl:380-393` `_replace_current_body_children` | document |
| serialized DOM reconciliation | `browser_session_runtime.spl:557-583` `_sync_body_html_from_dom` / `_sync_runtime_body_from_dom` | document, only when serialized body changed |
| event/default actions | `browser_session_runtime.spl:645-737` `dispatch_dom_event` | route through the two owners above |
| text/select/focus edits | `browser_session_runtime.spl:1009-1079,1128-1171` | route through the two owners above |
| document commit/reset | `browser_session_runtime.spl:1294-1375` `_load_page_source` | document + style + resource |
| JS bridge sync/title | `browser_session_runtime.spl:1479-1686` `_sync_from_runtime` | document |
| Simple Script body/title | `browser_session_loading.spl:314-363` | document |
| decoded image replacement | `browser_session_loading.spl:502-548` | resource |
| stylesheet finalize/Stop | `browser_session_loading.spl:950-995` | style |

The existing `_advance_ui_access_revision` at
`browser_session_runtime.spl:374-378` is completed and exposed as
`document_revision`; no second structural revision is added. Title-only
changes in `browser_session.spl:1635-1652` and
`browser_session_loading.spl:767-773,836-859` must advance it; body changes
there must route through `_replace_current_body_children`, not update the
detached `current_body_html` string alone.

The snapshot API is deliberately small:

```text
render_revisions() -> BrowserRenderRevisions
render_snapshot_since(document_revision, style_revision)
  -> BrowserRenderSnapshot
```

The second method supplies `document_html` only when either input revision is
stale. The consuming `SimpleWebRenderSession` increments `serialize_count`
when that snapshot contains HTML. Resource-only, scroll, overlay, and unchanged
frames do not serialize.

Implementation is split into three conflict-free batches:

1. Add the failing counter/invalidation SSpecs, repair BrowserSession revision
   ownership, and expose conditional `BrowserRenderSnapshot`. No renderer
   cache yet.
2. Add `SimpleWebRenderSession` beside the canonical layout renderer and move
   the existing `parse_html` through Draw-IR body at
   `simple_web_html_layout_renderer.spl:869-1038` behind its stage methods.
   First prove exact unchanged reuse and bounded reset/close.
3. Replace `_worker_frame`'s unconditional serialize/rebuild at
   `hosted_browser_renderer_worker.spl:153-167` with the one session. Then
   enable parse/CSS/base-style reuse for animation, raw-layout reuse for
   scroll/overlay, and paint-only image invalidation.

Implementation status (2026-07-29): batches 1-3 are complete only for the
smallest exact unchanged-frame/close slice. The session retains one existing
combined semantic/layout/Draw IR result and reruns the canonical full render
for dirty keys. Mutation-site completion and every stage-selective
invalidation named above remain open and fail-fast.

The batch-one resource contract compares `resource_revision` without forcing
HTML serialization. Binding add, decoded resource replacement, failed-binding
removal, pruning, and document replacement advance it. Active and stopped
stylesheet finalization advance `style_revision`, including completion after
an earlier network-wait frame. Worker close calls the BrowserSession close
owner, which drops document source/DOM/history, image resources and bindings,
pending/inflight/load state, runtime/timers, overrides, and animation state
before the worker can be retained for inspection.

No batch adds Draw-IR diffing, partial damage, per-node invalidation, or a
second pixel cache. Those wait for measured retained-session evidence.

## Engine2D lifecycle

- create backend/device/font owner once at browser/app start;
- submit accepted Draw IR on dirty frames;
- read back only in explicit evidence mode;
- resize replaces the device exactly once when required;
- navigation retains compatible engine/font state;
- app close shuts down once;
- pixel-buffer overrides are released on replacement and owner disable or
  shutdown; another backend cannot clear the active owner.

Atlas/cache/face handles never appear in Draw IR.

## GC and resource lifecycle

Document-owned registries:

- DOM nodes and listener lists;
- JS objects/promises/microtasks;
- timers/rAF callbacks;
- pending requests/responses;
- decoded images/resources;
- styles/layout/Draw IR.

On stop/navigation/close:

1. invalidate generation;
2. cancel request/script/timer work;
3. remove listener/callback references;
4. clear DOM/resource/style/layout/composition references;
5. compact completed/canceled registries;
6. allow normal GC;
7. sample memtrack/heap/RSS after bounded quiescence.

Cached back/forward navigation commits reset the worker scroll owner before the
first restored-document frame; stopped or rejected navigation leaves it intact.

No manual collection is added merely to make the soak pass. A retained root is
fixed at its owner.

## Limits

All defaults are compile-time constants with bounded production overrides:

- IPC envelope: reuse existing 1 MiB ceiling;
- URL/header/body/decoded resource;
- redirects/connections;
- DOM nodes: 65,536 per parsed document; depth/attributes/text are also bounded;
- HTML parse work: 262,144 tokens, 65,536 retained attributes, and a 1 MiB
  direct-render source / 262,144 structural-part ceiling;
- CSS parse work: 6,000 bounded candidates per block and 4,096 admitted rules
  per document, with opening/closing brace structure truncated before split,
  variable output bounded to 1 MiB/16 fallback levels, and selector groups/parts
  bounded to 256 per rule; keyframe offsets/declarations are also capped at 256;
- script source/jobs/microtasks/timers;
- active-load and committed warnings: 128 unique entries, 4096 bytes each;
- frame callbacks and work time;
- Draw IR commands/strings/images/pixels;
- renderer RSS/CPU/wall time;
- renderer restart rate.

BrowserSession node-limit failures return `resource_limit` before document
replacement. Direct rendering allocates at most the fixed node arena and
renders the admitted prefix.

## Errors

Stable public codes:

- `invalid_url`
- `unsupported_scheme`
- `disabled`
- `stale_target`
- `target_not_found`
- `unsupported_operation`
- `stale_navigation`
- `tls_validation_failed`
- `origin_denied`
- `csp_denied`
- `mixed_content_denied`
- `sandbox_unavailable`
- `capability_denied`
- `resource_limit`
- `renderer_crashed`
- `action_failed`

Diagnostics include code, phase, generation, and safe counters only.

## Performance evidence

Measure:

- warm/cold startup;
- navigation to first contentful frame;
- changed and unchanged frame times;
- input-to-present;
- parse/style/layout/paint time/count;
- renderer RSS, memtrack count/bytes, heap registry;
- node/listener/timer/request/layout/command counts;
- Engine2D/device/font create/shutdown counts;
- final 5,000-cycle slope in a 10,000-cycle soak.

The first implementation may use full-frame dirty rasterization. Partial damage
is added only if the selected targets cannot be met and profiling identifies
paint bandwidth as the cause.

## Compatibility manifests

Supported HTML/CSS/WPT and JavaScript/Test262 cases are pinned by revision and
explicit allowlist. A pass means every claimed row passes. Unsupported rows are
visible and cannot be silently skipped into the score.

## Rollout order

1. Fix false-green evidence and add fail-fast scenario contracts.
2. Remove ambient Node/file authority from browser profile.
3. Add navigation generation and address action fix.
4. Establish live DOM/event/default-action path.
5. Add persistent render session and one clock.
6. Wire broker Fetch/TLS/origin/cookie policy.
7. Establish platform sandboxed renderer.
8. Fix retained roots and measured performance regressions.
9. Run conformance, security, platform, soak, and release verification.

## Current bounded behavior

- Attribute selectors add `10` specificity per bracketed selector.
- Browser and interpreter clocks advance even when no timer is currently due,
  so later timers use their creation time rather than document epoch.
- Same-document discrete renderer commands queue FIFO to a hard limit of 64;
  overflow fails closed and navigation-related operations never accept stale
  queued input.
- Resolved font advances remain typed from Draw IR construction through SDN and
  Engine2D; legacy CSV is read-only compatibility input.
- Chromium capture denies popups/navigation and all production Chromium launch
  paths retain the Electron renderer sandbox.
- Renderer startup and successful Favorite toggles receive one bounded,
  canonical bookmark snapshot from the parent-owned profile store. Favorite
  rejects renderer-busy before committing profile state.
- Renderer response IPC contains no Set-Cookie headers; only the parent cookie
  jar persists and attaches transport cookies.
- Form reset uses captured parse defaults, shared form ownership, and one
  cancelable bubbling event before mutation.
- Built-in font aliases share one cache entry per resolved font path; custom
  faces are not admitted to the process-lifetime default cache.
- Live Electron screenshot proof is accepted only when decoded PNG pixels
  exactly reproduce its checksum, nontransparent count, and distinct-color
  count; compressed and inflated PNG data are each capped at 160 MiB.
- External `<img src>` is intentionally not claimed complete. Completion
  requires a bounded broker image request, CSP/HSTS/mixed-content enforcement,
  decoded pixels in layout/Draw IR, and an HTTPS subdomain-HSTS pixel scenario
  with a mixed-content-blocked control.
## External PNG image rendering (2026-07-29)

- Discover at most 64 distinct authored `<img src>` values and retain both the
  authored key and resolved fetch URL.
- Admit only canonical lowercase-hex `image/png` responses after broker policy
  and strict bounded PNG/zlib/DEFLATE validation.
- Cap a document at 131,072 decoded image pixels. Emit the image after its box,
  applying object-fit, object-position, and ancestor/content clipping.
- Carry resources in additive `SBRF5`; legacy render/frame APIs delegate with an
  empty resource list.

## CSS URL background rendering (2026-07-29)

- Discover bounded `url(...)` values from inline declarations and admitted
  linked stylesheets. Inline declarations use the authored URL as their Draw-IR
  resource key; linked CSS is rewritten to the canonical resolved URL.
- Reuse the image request, CSP `img-src`, HSTS, mixed-content, PNG decode, and
  document resource limits already owned by BrowserSession and the broker.
- Lower only the supported single URL layer into one typed Draw-IR background
  image carrying size, position, repeat, origin, and clip geometry. Paint it
  after the element color and before content, then repaint the canonical border
  overlay.
- Filter the document image table to composition-referenced resources before
  additive `SBRF5` encoding. Preserve the existing retained-frame and CSS
  animation scheduling contracts.
- Keep multiple image layers and fixed/local background attachment fail closed
  until dedicated bounded-policy and exact-pixel coverage exists.

## Post-load resource, timer, transport, and sandbox design (2026-07-29)

- After script reconciliation mutates the DOM, collect newly visible background
  URL sources and pass them to `_start_image_source`. The request carries its
  authored `image_resource_key`; response commit stores pixels under that key
  so Draw IR resolves the same resource without another resolver.
- Reuse `admitted_image_sources` for deduplication. Stop or navigation
  generation cancellation rejects late responses before image state changes.
  Successful commit invalidates rendering but preserves animation epochs.
- Timer drain performs the existing bounded due-task scan, updates an interval
  slot in place, and removes a completed one-shot slot in place. `clearTimer`
  removes its matching slot directly; no queue copy or tombstone set is added.
- `begin_stop` sets `stop_after_write` only after bytes of the current command
  have left the broker. `_begin_stop_after_write` runs when `pending_wire`
  empties, clears provisional navigation/network state, and sends one Stop. The
  worker feeds its existing decoder an empty chunk while messages remain.
- `_browser_transport_host` unwraps only a canonical bracketed IPv6 literal;
  URL/history/origin stay bracketed. DNS names, IPv4, and malformed brackets
  pass through unchanged.
- Final Linux renderer seccomp includes `get_robust_list`; stage-one admission
  and stage-two ownership remain unchanged.

Focused host C containment/TLS checks pass. Pure-Simple runtime/spec execution
remains blocked by the recorded compiler defect, so no runtime PASS, manual
refresh, bootstrap, or Rust-seed fallback is claimed.

## Frame, chrome, and shared-profile convergence (2026-07-29)

- A CSS background command carries `background-shape-{x,y,width,height}` and
  `background-radius-{tl,tr,br,bl}-{x,y}` beside its tile metadata. Engine2D validates
  unique canonical integers, tests the rounded shape in the sampling loop, and
  charges successful command area against a single `framebuffer width * height`
  composition budget.
- `content_paint_hidden_by_ancestor` rejects a zero-opacity node and descendants of
  any zero-opacity ancestor during paint emission. **PROPOSED / UNIMPLEMENTED:**
  computed style must retain independent `css_opacity_pct` and
  `filter_opacity_pct` integers. CSS opacity must be in `0..100`: zero must use
  the existing subtree suppression, 100 must stay inline, and only `1..99` may
  emit `group(child_batch_id, css_opacity_pct)`. Paint must put the element
  subtree in one child batch and insert that command at its original paint
  position. Every non-root batch must have exactly one incoming reference.
  Encode/decode/protocol admission must validate the complete graph and checked
  sums before transient allocation: one root, unique IDs, known targets, no
  orphan or multiply referenced child, no cycle, depth at most 512, aggregate
  commands at most 1,024, batches at most 1,025, payload at most 1,048,576
  bytes, and command plus clipped-group areas at most
  `viewport_pixels * 16`.

  Alpha conversion and blending must be integer-exact. Let
  `round255(x) = (x + 127) / 255`. The group alpha byte must be
  `(css_opacity_pct * 255 + 50) / 100`. Applying a group must use
  `src_a = round255(child_a * group_alpha)` and
  `src_p = round255(child_p * group_alpha)` for each already-premultiplied
  channel. Premultiplied source-over must then use
  `out_a = src_a + round255(dst_a * (255 - src_a))` and
  `out_p = src_p + round255(dst_p * (255 - src_a))`, with nearest-integer
  unpremultiplication
  `(out_p * 255 + out_a / 2) / out_a` (or zero when `out_a == 0`) only when a
  straight-ARGB consumer requires it. No sibling helper batch, private web
  compositor, second pixel budget, or
  `filter_opacity_pct` fallback must be added. The nested oracle must place a
  blue box at 50% inside a same-bounds transparent/no-paint parent at 50%, over
  white; only blue must receive the effective 25% alpha and the result must be
  `0xFFBFBFFF`.
- Bookmark persistence is read once through `BrowserProfileStore`. A host
  snapshot revision is applied independently to the primary renderer and
  `HostedBrowserRendererRegistry`; new entries start at revision zero and
  receive the current snapshot on their first idle turn.
- Escape ends address editing and restores `document_url` when committed,
  otherwise the startup address retained by that window. Enter clears editing
  only after `begin_navigate` succeeds; frame commit later replaces the draft.
- Both in-process and sandbox HTTP jobs call
  `hosted_browser_transport_host`; only a parsed bracketed IPv6 literal is
  unwrapped for socket/TLS, while canonical URL state is unchanged.
- A deferred resize replaces an adjacent queued resize (and identical
  dimensions are ignored). Render paths compute `render_html_document()` once
  per frame and reuse it for animation reconciliation and layout.

## HSTS provenance, script reclamation, and empty atomic baselines (2026-07-29)

- `_finalize_network` never accepts transport-authentication input. Only the
  successful parsed completion of the existing platform HTTPS job may apply a
  Strict-Transport-Security header. Generic/mock/plain/error paths finalize
  content without changing HSTS state.
- `SimpleScriptExecutor.reset()` creates the next document event loop, rebinds
  the existing runner to the new DOM/loop/console owners, and clears callback
  IDs, callback source bodies, timers, rAF work, and document console entries.
- Inline line layout computes a shared baseline from signed parent-strut
  leading and supported empty atomic margin boxes, then shifts complete layout
  subtrees before Draw IR. The supported slice resolves positive pixel margins;
  unsupported negative/percentage margins, non-empty last-line baselines, and
  overflow baselines stay ledgered.
- Live trusted/invalid-certificate HSTS evidence remains fail-fast until an
  admitted production HTTPS artifact is available. The current hosted-WM
  wrapper also remains non-qualifying while its exact-byte runtime admission
  lacks trusted production build provenance.

## Two-layer CSS and material-witness refinement (2026-07-29)

- `background-image` accepts exactly two URL layers only after both traverse
  the existing resource policy. Shared scalar background longhands apply to
  both; missing, denied, malformed, and unsupported pairs emit neither layer.
- Paint emits the back layer then front layer through existing typed Draw IR
  and adds the existing border overlay only after the complete set lowers.
- Visible material witness lines use preallocated indexed lists plus one join;
  hashes, order, culling, animation scheduling, and composition stay unchanged.
