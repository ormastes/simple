# Shared UI Contract

**Date:** 2026-04-04
**Status:** Active
**Scope:** Defines the exact shared UI abstraction, protocol, and behavior contract across supported surfaces.

## 1. Purpose

This document is the authoritative source of truth for the shared UI contract. All supported surfaces MUST implement this contract. All shared tests MUST assert against this contract, not surface-specific behavior.

## 2. Supported Surfaces

The shared UI contract has two layers:

1. **Semantic UI contract** - the backend-neutral widget tree, state snapshot,
   command/event vocabulary, and read-after-write behavior. This layer applies
   to TUI, GUI, web, Electron, Tauri, and headless adapters.
2. **Protocol contract** - the concrete HTTP/WebSocket `/api/test/...` API used
   by network-addressable surfaces. This layer is stable today for Web Backend
   and TUI-Web Proxy only.

### Semantic-Contract Surfaces

| Surface | Transport | Module | Stage | Notes |
|---------|-----------|--------|-------|-------|
| Native TUI | Direct terminal rendering | `app.ui.tui` | S1 target | Must expose the same semantic tree, command vocabulary, focus state, and captures through adapter helpers; it is not required to speak HTTP. |
| Web Backend | HTTP + WebSocket | `app.ui.web` | S4 | Full HTML rendering, browser client, and `/api/test` endpoints. |
| TUI-Web Proxy | HTTP + WebSocket | `app.ui.tui_web` | S4 | TUI rendered as HTML over network. |
| Electron | IPC stdin/stdout + WebView bridge | `app.ui.electron` | S2 target | Host IPC is adapter-private; render, snapshot, patch, input, capability, and host-window envelopes come from the shared API. |
| Tauri | IPC stdin/stdout + WebView bridge | `app.ui.tauri` | S2 target | Host IPC is adapter-private; render, snapshot, patch, input, capability, and host-window envelopes come from the shared API. |
| Pure Simple GUI | Engine2D/Web renderer bridge | `app.ui.web`, `std.gpu.browser_engine` | S3 target | GUI state must flow through semantic UI, then shared web render artifacts, then Engine2D-backed pixels when requested. |
| Headless | In-memory adapter | `app.ui.none` | S1 target | No interaction surface, but can expose semantic state for tests and automation. |

### Maturity Stages

| Stage | Meaning | Required Evidence |
|-------|---------|-------------------|
| S0 Adapter-only | Surface exists but has no shared semantic snapshot. | Adapter is documented as out of shared assertions. |
| S1 Semantic state | Surface exposes `ElementInfo`, `UIStateInfo`, protocol version, and capability state through a shared helper. | Shared state query tests pass for the surface. |
| S2 Semantic events | Surface accepts shared semantic commands/events and reports dispatch results. | Click/type/key/focus/resize command tests pass with read-after-write checks. |
| S3 Shared renderer | Surface render/snapshot/patch/input envelopes are produced by the shared render API or a documented renderer bridge. | Envelope parity tests pass and renderer-specific transport is adapter-only. |
| S4 Protocol stable | Surface exposes the stable HTTP/WebSocket `/api/test` protocol. | Protocol endpoint tests pass. |

The next implementation target is to move Native TUI and headless to S1/S2,
Electron and Tauri to S2/S3, and pure Simple GUI/web to S3 with Engine2D-backed
capture evidence. Web and TUI-Web remain the only S4 surfaces today.

### Protocol-Stable Surfaces

| Surface | Transport | Module | Notes |
|---------|-----------|--------|-------|
| Web Backend | HTTP + WebSocket | `app.ui.web` | Full HTML rendering, browser client |
| TUI-Web Proxy | HTTP + WebSocket | `app.ui.tui_web` | TUI rendered as HTML over network |

### Adapter Boundary

Different transports are allowed below the semantic contract. Native TUI does
not need HTTP; Electron and Tauri may keep IPC/WebView bridges; headless may
keep in-memory state only. These adapters must not invent a different widget
kind vocabulary, focus model, command meaning, render-envelope schema, or
capability vocabulary when participating in shared tests.

`src/lib/common/ui/semantic_contract.spl` is the code owner for the S1 and S2
surface-neutral API. It defines protocol version, semantic element/state
records, semantic command/event types, dispatch result, snapshot helpers, and
transport-independent capability records. It reuses the existing UI access
snapshot substrate instead of creating a competing widget tree. `RenderBackend`
remains the low-level render/event/capability interface; it is not the semantic
UI contract by itself.

### Out of Scope

- Pixel-perfect rendering fidelity
- CSS/browser layout assertions
- Terminal emulator quirks
- Platform-specific key codes
- Requiring every staged surface to expose `/api/test` before it exposes the
  shared semantic model

## 3. Protocol Contract

### 3.1 Protocol Version

All responses from the shared test API MUST include a protocol version header or field:

```
X-UI-Protocol-Version: 1
```

Version 1 is the initial stable contract defined in this document.

### 3.1.1 Protocol Version 2 Draw IR Extension

Protocol v2 is an additive, capability-gated extension for Draw IR inspection.
It does not replace Protocol v1 element/state/action endpoints.

Surfaces that support the extension advertise a Draw IR capability and return:

```text
X-UI-Protocol-Version: 2
```

The extension endpoints are:

| Endpoint | Response | Description |
|----------|----------|-------------|
| `/api/test/draw-ir` | Draw IR JSON or SDN text | Current composition for the active surface |
| `/api/test/draw-ir?id=X` | Draw IR JSON or SDN text | Composition filtered to a stable node/surface id |
| `/api/test/draw-ir/diff` | Geometry/style diff JSON | Semantic Draw IR delta by stable id |
| `/api/test/draw-ir/layout?id=X` | Layout JSON or SDN text | Box geometry for a stable node/surface id |

Client helpers such as `expect_draw` are SPipe-layer conveniences over these
endpoints. They run inside ordinary specs that import `use std.spec`; the
existing `std.spipe` alias remains source-compatible.

### 3.2 Base URL

All shared test endpoints live under `/api/test/`. Application-specific endpoints are outside this contract.

### 3.3 Endpoints

#### Read Operations (GET)

| Endpoint | Response | Description |
|----------|----------|-------------|
| `/api/test/ready` | `{"ready":true,"protocol_version":1}` | Server readiness check |
| `/api/test/element?id=X` | `ElementInfo` JSON | Single element by ID |
| `/api/test/elements` | `[ElementInfo]` JSON array | All elements |
| `/api/test/state` | `UIStateInfo` JSON | Application state snapshot |
| `/api/test/screenshot` | HTML string | Full widget tree as HTML |

#### Write Operations (POST)

| Endpoint | Body | Response | Description |
|----------|------|----------|-------------|
| `/api/test/click` | `{"id":"X"}` | `{"ok":true}` | Click element |
| `/api/test/type` | `{"id":"X","text":"Y"}` | `{"ok":true}` | Type text into element |
| `/api/test/drag` | `{"from_id":"X","to_id":"Y"}` | `{"ok":true}` | Drag between elements |
| `/api/test/submit` | `{"id":"X"}` | `{"ok":true}` | Submit form/dialog |
| `/api/test/event` | Event JSON (see 3.5) | `{"ok":true}` | Raw event injection |

Draw IR extension endpoints are listed in §3.1.1 because they require Protocol
v2 capability advertisement.

### 3.4 Error Model

All errors MUST use this shape:

```json
{"error": "<error_code>", "message": "<human_readable>"}
```

Standard error codes:

| Code | HTTP Status | When |
|------|-------------|------|
| `not_found` | 404 | Route not found |
| `element_not_found` | 404 | Element ID does not exist |
| `method_not_allowed` | 405 | Wrong HTTP method |
| `missing_field` | 400 | Required field absent in body |
| `invalid_field` | 400 | Field value is malformed |
| `unsupported_action` | 400 | Action not supported on this surface |
| `stale_session` | 410 | Session expired or reset |
| `unknown_event_type` | 400 | Unrecognized event_type value |

### 3.5 Event Types

The `/api/test/event` endpoint accepts these event types:

| event_type | Required Fields | Description |
|------------|----------------|-------------|
| `key` | `key` | Single key press |
| `action` | `name` | Named action dispatch |
| `quit` | (none) | Quit signal |
| `focus_next` | (none) | Move focus forward |
| `focus_prev` | (none) | Move focus backward |
| `resize` | `width`, `height` | Viewport resize |

## 4. Data Model Contract

The data model is semantic first. HTTP JSON, Electron IPC, Tauri IPC, terminal
test helpers, and headless snapshots are transport encodings of the same model.
Tests may use transport-specific capture mechanisms, but assertions about UI
state must target the fields below.

### 4.1 ElementInfo

Every element returned by the protocol MUST include these fields:

```json
{
  "id": "string",
  "kind": "string",
  "visible": true,
  "focused": false,
  "enabled": true,
  "selected": false,
  "text": "",
  "props": {}
}
```

| Field | Type | Semantics |
|-------|------|-----------|
| `id` | text | Unique identifier, stable across renders within a session |
| `kind` | text | Widget type: panel, button, text_field, label, checkbox, dropdown, etc. |
| `visible` | bool | Element is in the render tree and not hidden |
| `focused` | bool | Element has input focus |
| `enabled` | bool | Element accepts interaction (not grayed out) |
| `selected` | bool | Element is in selected state (checkbox checked, list item selected) |
| `text` | text | Primary text content (label text, input value, etc.) |
| `props` | object | Additional key-value properties |

### 4.2 UIStateInfo

```json
{
  "mode": "NORMAL",
  "focused_id": "string",
  "title": "string",
  "theme": "string",
  "element_count": 0,
  "protocol_version": 1
}
```

| Field | Type | Semantics |
|-------|------|-----------|
| `mode` | text | Application mode (NORMAL, INSERT, COMMAND, etc.) |
| `focused_id` | text | ID of the currently focused element |
| `title` | text | Application/window title |
| `theme` | text | Current theme name |
| `element_count` | i32 | Total number of elements in tree |
| `protocol_version` | i32 | Protocol version (always 1 for this contract) |

### 4.3 Widget Kind Vocabulary

Canonical widget kind values (used in `ElementInfo.kind`):

| Kind | Focusable | Text | Interaction |
|------|-----------|------|-------------|
| `panel` | no | container label | none |
| `button` | yes | button label | click |
| `text_field` | yes | input value | type, submit |
| `label` | no | display text | none |
| `checkbox` | yes | label | click (toggle) |
| `dropdown` | yes | selected value | click (open) |
| `list` | yes | (via children) | click, navigate |
| `table` | yes | (via children) | click, navigate |
| `tabs` | yes | active tab label | click |
| `dialog` | no | title | submit, close |
| `menu` | yes | (via children) | click, navigate |
| `progress` | no | percentage/label | none |
| `textarea` | yes | content | type |
| `scroll` | no | (via children) | scroll |
| `tree` | yes | (via children) | click, navigate |
| `image` | no | alt text | none |
| `statusbar` | no | status text | none |
| `heading` | no | heading text | none |
| `divider` | no | (none) | none |
| `tooltip` | no | tooltip text | none |

### 4.4 Wire vs Internal Types

The internal model (`WidgetRecord`, `WidgetNode`, and their helpers) uses typed enums — `WidgetKind`, `LayoutKind`, `ThemeId`, `Spacing`, `Radius`, `Elevation`, `SurfaceRole`, `TextRole` — delivered in Phases 2-4 of `doc/05_design/ui_typed_core_rfc.md`.

The wire protocol (UiAccessSnapshot JSON, IPC v1) uses canonical **text strings** for interoperability and backwards compatibility. The codec boundary sits on each enum via `to_wire()` / `from_wire()` co-located methods.

```
Internal model                    Wire / IPC
──────────────────────────────    ──────────────────────────────
WidgetKind.Panel        ──►  "panel"      (ElementInfo.kind)
LayoutKind.Column       ──►  "column"     (props map)
ThemeId.Obsidian        ──►  "obsidian"   (UIStateInfo.theme)
Spacing.Md              ──►  "12"         (resolved px value)
SurfaceRole.Card        ──►  "card"       (props map)

                        ◄──  from_wire()  (deserialization path)
```

Application code works exclusively with the typed enums. Only the serialisation layer (`to_wire()` / `from_wire()`) touches the string form. Tests MUST assert on `ElementInfo.kind` string values (per §7), not on internal enum identities.

## 5. Interaction Semantics

### 5.1 Mandatory Interactions (All Shared Surfaces)

| Action | Semantics |
|--------|-----------|
| click | Activate the target element (button press, checkbox toggle, list select) |
| type | Focus target, then inject character-by-character key presses |
| submit | Trigger form/dialog submission on the target or its parent form |
| focus_next | Move focus to the next focusable element in tab order |
| focus_prev | Move focus to the previous focusable element in tab order |
| drag | Focus source element, dispatch drag action to target |
| key | Inject a single named key press |
| action | Dispatch a named action string |

### 5.2 Surface-Specific Extensions

These interactions MAY be supported but are not required by the contract:

- scroll (viewport-dependent)
- hover (mouse-dependent)
- right-click / context menu
- touch gestures
- window resize below minimum

### 5.3 Event Ordering

- Events are processed in FIFO order within a single connection.
- There is no ordering guarantee across concurrent connections.
- After a POST action, a subsequent GET MUST reflect the state change caused by that action (read-after-write consistency).

## 6. Session Semantics

### 6.1 Lifecycle

| Phase | Semantics |
|-------|-----------|
| Create | Server starts, loads UI definition, initializes widget tree |
| Ready | Server responds to `/api/test/ready` with `{"ready":true}` |
| Active | Server processes requests, maintains widget state |
| Reset | Not currently supported; restart server for clean state |
| Teardown | Server stops, connections close, state is discarded |

### 6.2 Session Isolation

- Each server instance is a single session.
- Multiple test clients connecting to the same server share session state.
- Tests requiring isolation MUST use separate server instances on different ports.

### 6.3 Stability

- Element IDs are stable within a session (same UI definition produces same IDs).
- Element IDs are deterministic across sessions for the same UI definition file.
- Widget tree structure may change after events (dialog open/close, list changes).

## 7. Assertion Contract

Tests MUST only assert against:

| Category | Assertable | Not Assertable |
|----------|-----------|----------------|
| Identity | element ID, element kind | internal DOM structure |
| State | visible, focused, enabled, selected | CSS classes, styles |
| Content | text field value, label text | rendered pixel output |
| Structure | element exists, element count | absolute position |
| Behavior | click causes state change | animation timing |

## 8. Deviations Register

Surface-specific deviations from this contract MUST be documented here:

| Surface | Deviation | Reason | Workaround |
|---------|-----------|--------|------------|
| TUI-Web | `screenshot` returns ANSI-to-HTML | TUI renders to ANSI first | Assert on text content, not HTML structure |
| TUI-Web | Viewport fixed 80x24 | Terminal size convention | Use `resize` event to change |

## 9. Support Matrix

| Capability | Web Backend | TUI-Web Proxy |
|------------|-------------|---------------|
| `/api/test/ready` | yes | yes |
| `/api/test/element` | yes | yes |
| `/api/test/elements` | yes | yes |
| `/api/test/state` | yes | yes |
| `/api/test/screenshot` | yes | yes |
| `/api/test/click` | yes | yes |
| `/api/test/type` | yes | yes |
| `/api/test/drag` | yes | yes |
| `/api/test/submit` | yes | yes |
| `/api/test/event` | yes | yes |
| Protocol version header | yes | yes |
| Structured error model | yes | yes |
| Stable element IDs | yes | yes |
| Read-after-write consistency | yes | yes |
| ElementInfo.enabled | yes | yes |
| ElementInfo.selected | yes | yes |
| ElementInfo.text | yes | yes |
| UIStateInfo.element_count | yes | yes |
| UIStateInfo.protocol_version | yes | yes |
| Protocol v2 Draw IR extension | optional | optional |

## 10. Versioning

- This is **Protocol Version 1**.
- Breaking changes (field removal, semantic change) require a version bump.
- Additive changes (new optional fields, new endpoints) do not require a version bump.
- Clients SHOULD check `protocol_version` in the ready response and fail fast if unsupported.
- Protocol Version 2 is reserved for the optional Draw IR inspection extension;
  clients must feature-detect it before calling `/api/test/draw-ir*`.
