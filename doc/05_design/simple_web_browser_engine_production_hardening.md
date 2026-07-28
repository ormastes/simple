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
8. Apply CORS/response filtering and MIME policy.
9. Update broker cookie jar.
10. Send only permitted response fields to renderer.

Hosted TLS applies one five-second budget across resolved connect attempts and
five-second socket read/write deadlines. A TLS read error or timeout invalidates
the runtime handle; H1 rejects the response instead of parsing or committing
partial bytes as an EOF-framed body.

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
animation mutations merge into a single invalidation before paint.

Scrolling preserves the real viewport dimensions so viewport-relative CSS
and flex layout do not change with scroll depth. Paint culls boxes wholly
outside that viewport before Draw IR submission.

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

No manual collection is added merely to make the soak pass. A retained root is
fixed at its owner.

## Limits

All defaults are compile-time constants with bounded production overrides:

- IPC envelope: reuse existing 1 MiB ceiling;
- URL/header/body/decoded resource;
- redirects/connections;
- DOM nodes/depth/attributes/text;
- script source/jobs/microtasks/timers;
- frame callbacks and work time;
- Draw IR commands/strings/images/pixels;
- renderer RSS/CPU/wall time;
- renderer restart rate.

Limit failures are typed and do not allocate the rejected payload.

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
