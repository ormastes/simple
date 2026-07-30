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

## RED detail contracts: overflow cascade and History API (2026-07-30)

- Extend the existing CSS rule record rather than adding a second cascade:
  retain origin, important bit, layer ID/order, specificity, and source order
  when parser output becomes `Rules`. The existing cascade owner resolves the
  winner, including CSS-wide values and shorthand/longhand interaction, then
  maps `overflow: clip` to a computed value separate from scroll-container
  modes. Parser flattening that erases this provenance is rejected.
- Replace the neighbor heuristic only when the wire contract can carry at most
  the existing 64 history entries, one checked current index, and a
  parent-issued document/origin/CSP witness. Decode into temporary bounded
  storage; validate sizes, index, canonical URLs, order, origin permissions,
  and every witness against the parent ledger; then swap the full ledger and
  index atomically. Any failure preserves committed chrome/history unchanged.

Both contracts are RED designs. They authorize no production or conformance
claim until modern SSpecs and an admitted pure-Simple executable prove them.

### Proposed cascade provenance detail (2026-07-30)

Status: **PROPOSED / UNIMPLEMENTED**.

Implementation order is deliberately narrow:

1. Change `CssRuleScan` to retain ordered layer paths/statements and replace
   `Rules` parallel declaration strings with typed `CssRule` /
   `CssRuleDeclaration` records. Predeclared, reopened, nested, and anonymous
   layers receive stable hierarchical identities only when their document-
   global enclosing `@media`/`@supports` conditions apply. Give every layer a
   separately ordered implicit outer sublayer for direct declarations. Keep
   raw custom-property tokens. Reject element-sensitive conditional layer
   registration until it has one document-global applicability owner.
2. Parse each declaration once, reject invalid values, expand supported
   shorthands, and assign per-declaration source order. Preserve origin,
   importance, encapsulation context, layer identity/path/order,
   element-attached style rank, and the matched selector specificity until the
   cascade owner selects a property winner.
3. Route tag defaults, presentational hints, matched author rules, and inline
   declarations through that owner. Presentational hints are zero-specificity
   author declarations before stylesheet rules; inline style retains its
   element-attached rank. Delete priority-string concatenation only after this
   route is complete.
4. Resolve `initial`, `inherit`, `unset`, `revert`, and `revert-layer` in the
   cascade owner from each property's sparse lower-candidate stack. Pass only
   winning ordinary computed values to the style field applier; `apply_decls`
   must no longer interpret CSS-wide values. Author `revert` removes animation
   candidates too. Element-attached `revert-layer` removes its attached tier
   before layer/origin fallback; this is required for important inline
   declarations under reversed important-layer order.
5. Route sampled animation declarations through the same owner below important
   origins, then replace overflow booleans with per-axis
   `CssOverflowMode`. Apply the visible/clip cross-axis computed rules. Only
   after these gates pass may `Clip` lower to paint clipping without creating
   scroll-container state. Retain separate computed and used pairs: viewport
   propagation maps used `Visible` to `Auto` and `Clip` to `Hidden`; replaced
   boxes map computed `Hidden` to used `Clip`; the default clip edge is
   padding-box plus zero clip margin.

The hot path uses one winner map per occupied cascade band. Each declaration
updates one property winner by specificity then source order; a single
precedence-ordered band walk handles layer reversal and CSS-wide rollback.
Stylesheet parse/layer state is document-generation cached. Selector,
presentational, and inline changes invalidate the affected node (and only
selector/inheritance-dependent descendants). Descendant mutation also
invalidates candidate `:has(...)` ancestors; insertion/removal/reorder
invalidates structural sibling/child cohorts and their dependent
ancestors/descendants. Viewport or support-condition truth changes rebuild the
applicable layer registry, compact ranks, selector buckets, and affected
styles; unchanged truth retains them. An animation tick overlays its sampled
properties on cached static winners.

Budgets are O(N) time, where N is candidate rules plus matched declarations,
and O(declarations) memory after the existing selector candidate lookup, with
no per-node rule sort, merged declaration string, raw declaration reparse, or
dense global-layer scan. Registry build precomputes band ranks; ranked selector
buckets reuse the existing sorted-list merge, and the node cascade traverses
only first-seen occupied bands. `occupied_bands <= matched_declarations`.
Debug receipts report parsed rules/declarations/layers, matched candidates,
occupied bands, resolved properties, cache hit/miss, and invalidated nodes
without logging CSS values.

The admitted first profile is light DOM with user-agent tag defaults, HTML
presentational hints, embedded author rules, inline style, and CSS animations.
User sheets, shadow encapsulation, `@scope`, and transitions remain explicit
unsupported inputs. Overflow promotion additionally requires separate RED
matrix rows for cross-axis computation, root/body viewport propagation,
replaced elements, float/BFC behavior, and hidden-versus-clip programmatic
scrolling; the first non-root/non-replaced slice is not full Cascade 5 or
Overflow 3 conformance.

Exact rollback controls are: normal top-level implicit-outer
`revert-layer` exposes the last explicit layer; important layer precedence is
reversed; non-attached important implicit-outer `revert-layer` falls to the
next origin, while important element-attached `revert-layer` exposes important
style-rule declarations; author `revert` ignores both author and animation
origins. Exact overflow controls are: `(Visible, Hidden)` computes to
`(Auto, Hidden)`, `(Clip, Scroll)` computes to `(Hidden, Scroll)`, root/body
propagation preserves source computed state while its element used state is
`Visible`, viewport used `Visible`/`Clip` map to `Auto`/`Hidden`, replaced
computed `Hidden` maps to used `Clip`, and default `Clip` pixels use the
padding box with zero clip margin.

The RED executable target is
`test/03_system/feature/web_platform/css/cascade_provenance_overflow_clip_spec.spl`.
Its exact visible steps are:

1. `Collect declaration provenance`
2. `Select cascade winners`
3. `Resolve CSS-wide values`
4. `Render overflow clip pixels`

Frozen helpers are `_setup_cascade_provenance_document`,
`_check_declaration_provenance`, `_check_cascade_winners`,
`_check_css_wide_values`, and `_check_overflow_clip_pixels`. Before
implementation every checker must fail explicitly with
`fail("RED: cascade provenance and overflow clip are unimplemented")`; no
placeholder pass is admissible.

Normative references:

- <https://www.w3.org/TR/css-cascade-5/#cascade-sorting>
- <https://www.w3.org/TR/css-cascade-5/#defaulting-keywords>
- <https://www.w3.org/TR/css-overflow-3/#valdef-overflow-clip>

<!-- codex-design -->
## RED detail contract: persisted bookmark titles (2026-07-30)

**Status: PROPOSED / UNIMPLEMENTED.**

### Shared interfaces

- `browser_bookmark_stored_title(raw_title: text) -> text` trims the title and
  returns it only when nonempty, NUL-free, and at most 512 UTF-8 bytes;
  otherwise it returns the existing empty-title sentinel.
- `browser_bookmark_title_or_url(stored_title: text, canonical_url: text) ->
  text` returns the validated stored title or the canonical URL. The fallback
  is computed for display and is not persisted in the title field.
- `BrowserRendererFrameDecodeResult` gains
  `document_title_present: bool` and `document_title: text`.
- `HostedBrowserRendererProcess` retains `document_title`,
  `document_title_url`, `document_title_generation`, and
  `document_title_reply_to_request_id` only for the latest accepted frame.

Both helpers live with the existing BrowserSession bookmark owner. All profile,
snapshot, and frame title limits use the existing O(1) UTF-8 byte-length helper
after trimming. No new module, database table, cache, or renderer command is
introduced.

### Wire and admission algorithm

1. The worker applies `browser_bookmark_stored_title(current_title)` and emits
   its result in the additive `SBRF8` title payload. The field length is the
   base64 payload length; decoded text must be valid UTF-8, NUL-free, and at
   most 512 bytes.
2. Before decode, `title-len` must be canonical decimal in `0..684`. Checked
   addition computes diagnostics, current/back/forward URL, title, image, and
   Draw-IR offsets and proves each end is ordered and inside the received
   payload.
3. Only after the checked offsets locate the title slice, a nonallocating
   alphabet/padding scan derives exact decoded length at most 512. Checked
   subtraction reserves both `title-len` encoded bytes and derived decoded
   bytes from the existing
   `BROWSER_RENDERER_MAX_PAYLOAD_BYTES` 1 MiB frame/Draw-IR budget before title
   decode or allocation.
4. Decode succeeds only when `base64_encode(decoded_title)` exactly equals the
   received title payload. Invalid UTF-8, NUL, noncanonical alphabet/padding,
   offset overflow/truncation/overlap, or budget exhaustion rejects the frame.
   The decoder accepts legacy `SBRF2..SBRF7` with no title witness. An empty
   `SBRF8` title means absent and remains a valid fallback case.
5. After existing message-generation and reply-ID admission, navigation commit,
   and current-history URL validation, the parent accepts the title only when
   the frame current URL exactly equals its canonical committed URL. Admission
   updates all four retained witness fields atomically.
6. Favorite toggle calls both shared helpers. Sandbox production uses the
   admitted title only when all retained witness fields still match the active
   generation, last accepted reply, and committed URL; otherwise its effective
   label is the canonical-URL fallback and persistence stores the empty
   sentinel. In-process production captures and validates
   `BrowserSession.current_title` before dispatch, commits that stored title,
   then reloads the canonical profile snapshot; it removes the current
   `add_favorite(url, url)` reconciliation.
7. `BrowserProfileStore` continues to store canonical URL plus a 0..512-byte
   title. `BrowserSession.load_bookmark_snapshot` preserves the empty sentinel,
   and UI-access bookmark nodes call `browser_bookmark_title_or_url`.

### Lifecycle and compatibility

- Navigation replacement clears the retained witness before a new request can
  accept Favorite. Favorite remains blocked while the renderer is busy.
- Site swap closes the old renderer and clears title state; the replacement
  generation cannot inherit it. Reload may reuse a URL only after its own frame
  reply supplies the new title.
- Profile/window/host restart restores the persisted title or empty sentinel
  through the existing revisioned snapshot. New and existing secondary
  renderers consume the same snapshot.
- Existing schema-version-1 databases require no migration. Existing
  URL-as-title rows remain valid. On load, a valid URL with an invalid title
  retains the bookmark with an empty title instead of exposing hostile text.
- A 512-byte UTF-8 title is accepted exactly. A 513-byte, empty, NUL-containing,
  stale-generation, stale-reply, or wrong-URL title cannot enter persistence;
  the visible label falls back to the canonical URL without changing its
  navigation target.

### Error handling

Protocol forgery fails the frame with the existing renderer-failure path.
Hostile document content merely produces an absent title witness and does not
deny rendering. Profile write/load failure preserves the prior immutable
snapshot and reports the existing profile error. No error may partially change
the bookmark URL, title, revision, or UI snapshot.

<!-- codex-design -->
## RED detail contract: renderer command capabilities (2026-07-30)

**Status: PROPOSED / UNIMPLEMENTED / RED.**

### Frozen interfaces

- `BrowserRendererCommandCapability` stores only canonical 32-byte lowercase
  hexadecimal text.
- `browser_renderer_command_capability_new() ->
  Result<BrowserRendererCommandCapability, text>` obtains exactly 16 bytes
  from an explicit-success hosted platform CSPRNG facade.
- `browser_renderer_command_capability_valid(value: text) -> bool` accepts
  exactly 32 lowercase hexadecimal ASCII bytes.
- `HostedBrowserRendererProcess` adds the staged fields
  `staged_generation`, `staged_root_request_id`,
  `staged_host_wire_request_id`, and `staged_hop_capability`, plus matching
  `issued_*` fields.
- `BrowserRendererMessage` adds `root_command_request_id` and
  `command_capability`.
- `_require_issued_renderer_reply(message, reply_to_request_id) ->
  Result<bool, text>` is the single parent-side admission helper.
- `_retire_renderer_command_capability()` clears the live hop binding without
  logging its value.

No capability registry, token cache, negotiation service, or public browser API
is added.

### Wire contract

`SBR2` has the bounded header:

`SBR2 kind generation wire-request-id root-command-request-id payload-bytes capability-bytes`

The wire body is `payload || capability-trailer`. `ready` alone has root ID
and capability length `0`; every host wire has capability length `32`. A
decoder bounds the header by 256 bytes, requires canonical decimal IDs and
lengths, proves `payload-bytes + capability-bytes` with checked addition, and
does not release the message until both are complete. It accepts only exactly
32 lowercase hexadecimal trailer bytes for a capability-bearing message.

`payload-bytes + capability-bytes` must be at most the existing
`BROWSER_RENDERER_MAX_PAYLOAD_BYTES` (1,048,576); the 32 trailer bytes reduce
available application payload rather than expanding the wire. Header plus
payload/trailer plus read-ahead remains bounded by the existing
`256 + 1,048,576 + 8,192` decoder limit. All generation/root/wire/reply IDs are
canonical decimal integers in `1..9223372036854775806`; ready alone uses root
ID `0`. Parsing rejects signs, leading zeroes, `9223372036854775807`, and
max-plus-one text before arithmetic. Registry/request increments are checked
and fail before mutation on exhaustion.

A root host command sets root ID equal to its wire request ID. Worker
`fetch_request` and `frame` messages echo that root ID, the immediately prior
host wire ID, and its one-use capability. `SBRN2 network_response` names both
the stable root ID and `reply_to_renderer_request_id` for the fetch wire it
answers, then carries a fresh tail capability for the worker's next
fetch/frame. Production host and worker reject `SBR1` and all legacy
request/frame/response revisions; no compatibility switch exists.

### Host algorithm

1. Before encoding any host wire, obtain a fresh capability. Entropy failure
   returns `renderer-command-entropy-unavailable` before pending state, wire
   bytes, deadline, or network state changes.
2. Installing a bounded wire fills only the `staged_*` tuple. The capability
   is the final trailer. `_flush_pending_wire_once` computes remaining bytes
   with checked subtraction; only the transition to exactly zero atomically
   moves staged generation/root/host-wire/capability into `issued_*`, clears
   `staged_*`, and advances expected reply state. Admission reads only
   `issued_*`. A partially written wire cannot be replaced or authorize a
   reply.
3. On renderer `fetch_request`, validate generation, root ID, one-use
   capability, and immediate reply ID through
   `_require_issued_renderer_reply`, then retire that capability. Only
   afterward may initiator/CSP/network policy run, cookies change, or an HTTP
   job start. The resulting `network_response` names the accepted fetch wire
   ID and obtains a fresh capability.
4. On a frame, perform the same binding check and retire its capability before
   frame/history/title/image decode or any renderer/registry transition. A
   deferred command obtains its own fresh capability only at activation.
5. `_cancel_pending_for_stop`, navigation replacement, timeout, protocol
   violation, network failure, `fail`, `close`, site swap, registry teardown,
   and terminal-frame acceptance all call the one retirement helper. Cleanup
   clears both staged and issued tuples. Stop/cancel preserves the last
   admitted display frame while retiring both tuples. Failure, close, site
   swap, and teardown additionally leave pending wire/root IDs empty, network
   handle zero, deferred commands empty, and retained image resources empty.

### Worker algorithm

The worker has no capability before fully decoding a host wire and its tail.
It copies that one token into exactly one generated fetch/frame and consumes
it. It accepts `SBRN2 network_response` only when generation/root ID match the
root command, `reply_to_renderer_request_id` equals its last fetch wire ID, and
the host wire ID is the next expected ID. That response supplies a fresh tail
capability for exactly one later fetch/frame. Tokens are omitted from
diagnostics and crash output.

### Entropy and lifecycle

The existing owner `src/lib/nogc_sync_mut/io/crypto_sffi.spl` adds
`secure_random_hex_exact(length: i64) -> Result<text, text>` and exports it
through `src/lib/nogc_sync_mut/io/__init__.spl`. It wraps the existing
`rt_random_hex` symbol but converts NIL, wrong length, or noncanonical output
to explicit failure. Native platform fill remains in
`src/compiler_rust/runtime/src/value/sffi/random.rs`; the symbol registry is
`src/compiler_rust/common/src/runtime_symbols.rs`. It returns exactly 16 bytes
or failure and never falls back to clock, PID, `rt_random_random`, or zeroes.

A separate runtime selfcheck build substitutes a failing fill function behind
`SIMPLE_RUNTIME_ENTROPY_SELFCHECK`; production has no fault switch. The system
fake renderer learns a real capability only by reading a complete host wire.
Restart evidence captures an old command tuple, replaces the renderer
generation, and proves the old generation is rejected as `stale-generation`.
A separately rewritten current-generation message carrying the retired old
capability is rejected as `unissued-renderer-reply`. A conforming control
reads the issued command, echoes its tuple, and reaches one accepted nonblank
frame.

### Ready defense in depth

Startup accepts only `SBR2 ready generation 1 0 0 0` and requires
`decoded.decoder.buffer_len == 0`. Any retained bytes fail with
`unexpected-ready-buffer`. This is an early diagnostic, not a substitute for
the per-command capability.

### Performance and observability

The process owns bounded counters only:
`renderer_capability_issue_count`, `renderer_capability_failure_count`,
`renderer_capability_staged_count`, `renderer_capability_consumed_count`,
`renderer_capability_reject_count`, a 64-bucket microsecond histogram, and
maximum generation latency. No token value is observable.

For warm commands, CSPRNG plus hex generation p95 is at most 1 ms and p99 is
report-only; total input-to-paint p95 remains the selected 50 ms
NFR-WEB-BROWSER-004 limit. Relative command-latency regression remains at most
5% under NFR-WEB-BROWSER-015. A zero-allocation token is not feasible with the
existing text wire: the selected target is exactly one transient 32-byte token
text allocation per host wire, zero retained capability allocations after
retirement, and no new collection or per-command subprocess.

After 10,000 command/fetch/frame cycles and bounded quiescence, staged and
issued capability counts and bytes are zero, heap/retained resources and RSS
return within 10% of post-warmup baseline (NFR-WEB-BROWSER-006/014), and browser
plus one renderer remains at most 384 MiB (NFR-WEB-BROWSER-005). The histogram,
allocation count, maximum RSS, post-warmup/final RSS, and failure/reject
counters are retained as evidence; p99 entropy latency is report-only until a
numeric NFR is selected.
