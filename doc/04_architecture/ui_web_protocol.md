# ui.web Wire Protocol — v1 Specification

## 1. Purpose & Scope

This document specifies the wire-level protocol spoken between the Simple `ui.web` server and any thin adapter (browser or native). The server is the sole authority over window state; the adapter renders patches and forwards raw input. The protocol transports three existing Simple types — `UiAccessSnapshot` (full retained-mode tree), `UIPatch` (incremental tree mutation), and `WmInputEvent`/`WmCreateRequest`/`WmCloseRequest`/`WmResizeRequest`/`WmMoveRequest` (window-manager commands) — over a single WebSocket connection per session. It is entirely unrelated to the 18 routes under `/api/test/*`, which remain on `src/app/ui.test_api/handler.spl` and are bit-identical to their current form; nothing in this protocol modifies or duplicates that path.

---

## 2. Transport

### v1 — WebSocket Secure (WSS)

- TLS is terminated by the existing `rt_tls_server_create` function in `src/lib/nogc_sync_mut/io/tls_ffi.spl`. No new TLS code is introduced.
- WebSocket framing uses the existing helpers in `src/app/ui.web/ws_handler.spl`:
  - `send_ws_text` — sends a UTF-8 text frame.
  - `compute_ws_accept` — produces the RFC-6455 `Sec-WebSocket-Accept` value.
- WebSocket parsing uses the existing helpers in `src/app/ui.web/async_ws.spl`:
  - `parse_ws_event` — parses an incoming frame from the TCP byte stream.
  - `extract_field` — pulls a named field from the JSON payload.
- Frame payload in v1 is JSON (UTF-8). Binary / CBOR framing is deferred to v2.
- One logical session per WSS connection. Multiplexing multiple sessions over one connection is not supported in v1.

### v2 (roadmap only — out of scope for this document)

- Raw TCP transport for native (non-browser) adapters.
- Binary / CBOR payload framing.

---

## 3. URL Namespace

| Endpoint       | Method / Upgrade | Handler (existing or forthcoming)                          | Notes |
|----------------|------------------|------------------------------------------------------------|-------|
| `/ui/login`    | POST             | `src/app/ui.web/server.spl` (`POST /ui/login` handler)    | Issues a signed 32-byte bearer token. Body: `{ "capability_grant": "<grant-id>" }` (v1 dev stub — full auth UX deferred). |
| `/ui/ws`       | WebSocket upgrade | `src/app/ui.web/ui_routes.spl`                            | Bearer-gated. Must carry `Authorization: Bearer <token>` header. |
| `/ui/resume`   | POST             | `src/app/ui.web/ui_routes.spl`                             | Resume semantics equivalent to `resume_session` message; returns `{ "session_id": "..." }`. |
| `/api/test/*`  | (unchanged)      | `src/app/ui.test_api/handler.spl`, `PROTOCOL_VERSION=1`   | **DO NOT TOUCH.** All 18 routes remain bit-identical. |

---

## 4. Handshake and Auth Sequence

```
Client                                     Server
  |                                           |
  |  POST /ui/login  { capability_grant }     |
  |------------------------------------------>|
  |  200 OK  { "token": "<bearer>" }          |
  |<------------------------------------------|
  |                                           |
  |  GET /ui/ws                               |
  |  Authorization: Bearer <token>            |
  |  Origin: https://allowed.example.com      |
  |  Upgrade: websocket                       |
  |------------------------------------------>|
  |  [server validates Origin against         |
  |   SIMPLE_UI_WEB_ALLOWED_ORIGINS,          |
  |   then calls session_token.verify(token,  |
  |   origin) — both checks BEFORE            |
  |   compute_ws_accept is called]            |
  |                                           |
  |  [on failure: HTTP 403 + close; no 101]   |
  |                                           |
  |  101 Switching Protocols                  |
  |<------------------------------------------|
  |                                           |
  |  --> hello { protocol_version, client_caps } |
  |  <-- capabilities { granted }            |
  |                                           |
  |  --> open_session { viewport }            |
  |      OR                                   |
  |  --> resume_session { session_id,         |
  |        snapshot_revision, last_sequence } |
  |                                           |
  |  <-- snapshot { ... }                     |
  |      OR patch_batch { ... }               |
  |           (depending on resume outcome)   |
```

### Auth detail

1. Client POSTs credentials to `/ui/login`. The server issues a 32-byte random token HMAC-signed over `(grant_id, origin, expiry_ms)` using the `CapabilityPolicy` grant id from `src/lib/common/security/enforcement/capability.spl`. The token is produced and verified by `src/app/ui.web/session_token.spl` (Phase 2 — new file): `issue(grant) -> Token` / `verify(token, origin) -> Result<Grant, AuthError>`.

2. Client opens WSS at `/ui/ws` carrying the bearer token in the `Authorization` header and a valid `Origin`.

3. Server calls `origin_guard.check(headers)` (from `src/app/ui.web/origin_guard.spl`, Phase 2 — new file) against the `SIMPLE_UI_WEB_ALLOWED_ORIGINS` environment variable. If the origin is not allowlisted, the server returns HTTP 403 and closes — the RFC-6455 handshake (`compute_ws_accept`) is never reached.

4. Server calls `session_token.verify(token, origin)`. On failure, HTTP 403 and close — again, before `compute_ws_accept`.

5. On success, `compute_ws_accept` is called and the 101 response is sent.

6. The first frame sent by the client after the 101 is `hello`. The server responds with `capabilities`. The client then sends `open_session` (new session) or `resume_session` (reconnect).

---

## 5. Message Table

All message payloads are carried inside the top-level envelope defined in Section 6.

| Message          | Direction | Fields                                                                                   | Maps to (existing Simple type / file)                                                                                                                          |
|------------------|-----------|------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `hello`          | C→S       | `protocol_version: u16`, `client_caps: u64` (bitset)                                    | `protocol_version` mirrors `UiAccessSnapshot.protocol_version` in `src/lib/common/ui/access.spl`; `client_caps` has no existing type — will be defined in `src/app/ui.web/session_token.spl` |
| `capabilities`   | S→C       | `granted: List<Capability>`                                                              | `Capability` enum in `src/lib/common/ui/capability.spl`                                                                                                       |
| `auth`           | C→S       | `bearer_token: bytes`                                                                    | Verified by `session_token.verify` in `src/app/ui.web/session_token.spl` (Phase 2)                                                                            |
| `open_session`   | C→S       | `viewport: Rect`                                                                         | `Rect` in `src/os/services/wm/window_protocol.spl`                                                                                                            |
| `resume_session` | C→S       | `session_id: text`, `snapshot_revision: u64`, `last_sequence: i64`                      | `snapshot_revision` corresponds to `PatchStream.snapshot_revision` (`src/lib/common/ui/patch_stream.spl`, Phase 1); `last_sequence` from `UiAccessSnapshot.sequence: i64` in `src/lib/common/ui/access.spl` |
| `snapshot`       | S→C       | Full `UiAccessSnapshot` tree + `revision: u64`                                           | `UiAccessSnapshot` in `src/lib/common/ui/access.spl`; encoded by `encode_snapshot` in `src/lib/common/ui/snapshot_wire.spl` (Phase 1)                         |
| `patch_batch`    | S→C       | `PatchEnvelope { session_id, snapshot_revision: u64, from_sequence: i64, to_sequence: i64, patches: List<UIPatch> }` | `PatchEnvelope` defined in `src/lib/common/ui/patch_wire.spl` (Phase 1); each patch is a `UIPatch` variant from `src/lib/common/ui/patch.spl`                 |
| `input_event`    | C→S       | `surface_id: text`, `widget_id: text`, `event: WmInputEvent`                            | `WmInputEvent` in `src/os/services/wm/window_protocol.spl`                                                                                                    |
| `window_cmd`     | C→S       | `cmd_type: text` (one of `"create"/"close"/"resize"/"move"`), `payload: object`         | Tagged union over `WmCreateRequest`, `WmCloseRequest`, `WmResizeRequest`, `WmMoveRequest` in `src/os/services/wm/window_protocol.spl`                          |
| `focus_changed`  | S→C       | `surface_id: text`, `widget_id: text`, `event: WmFocusEvent`                            | `WmFocusEvent` in `src/os/services/wm/window_protocol.spl`                                                                                                    |
| `resource_ref`   | S→C       | `surface_id: text`, `resource_id: text`, `url: text`, `etag: text`                      | No existing struct — fields will be defined as an ad-hoc record in `src/app/ui.web/web_runtime_adapter.spl` (Phase 3); `surface_id` resolves via `UiWindowSurfaceRegistry` in `src/lib/common/ui/window_surface_registry.spl` |
| `clipboard`      | both      | `op: "read"/"write"`, `mime: text`, `data: text`                                        | Gated by `ClipboardRead` / `ClipboardWrite` caps in `src/lib/common/ui/capability.spl`                                                                        |
| `ime`            | both      | `surface_id: text`, `compose_text: text`, `commit_text: text`, `cursor_pos: u32`        | Gated by `ImeCompose` cap (added in Phase 2 to `src/lib/common/ui/capability.spl`); no existing struct — will be defined in `src/app/ui.web/web_runtime_adapter.spl` |
| `ping`           | both      | `nonce: u64`                                                                             | No existing type; primitive field only                                                                                                                         |
| `pong`           | both      | `nonce: u64`                                                                             | Echo of `ping.nonce`; no existing type                                                                                                                         |
| `ack`            | C→S       | `last_applied_sequence: i64`                                                             | `sequence: i64` from `UiAccessEvent` in `src/lib/common/ui/access.spl`; drives GC in `access_store.spl`                                                       |
| `error`          | S→C       | `code: text`, `message: text`, `retry_after_ms: u64`                                    | No existing type; plain record — will be defined inline in `src/app/ui.web/web_runtime_adapter.spl`                                                            |

---

## 6. JSON Frame Encoding (v1)

Every frame is a single UTF-8 JSON object sent as a WebSocket text frame. The top-level envelope is:

```json
{
  "t": "<message_type>",
  "v": 1,
  "s": "<session_id>",
  "seq": <sequence_number_or_null>,
  "payload": { ... }
}
```

- `"t"`: message type string matching the `Message` column in Section 5.
- `"v"`: protocol version integer; always `1` in v1.
- `"s"`: session identifier string (server-assigned UUID); omitted (`null`) before `open_session` is acknowledged.
- `"seq"`: for `patch_batch`, the `from_sequence` value; for other messages `null` or omitted.
- `"payload"`: the message-specific object.

### Example 1 — `snapshot` frame

```json
{
  "t": "snapshot",
  "v": 1,
  "s": "550e8400-e29b-41d4-a716-446655440000",
  "seq": null,
  "payload": {
    "revision": 7,
    "protocol_version": 1,
    "root": {
      "surface_id": "surf-1",
      "widget_id": "root",
      "kind": "window",
      "props": {
        "title": "Terminal",
        "x": 100,
        "y": 80,
        "width": 800,
        "height": 600,
        "visible": true
      },
      "children": [
        {
          "surface_id": "surf-1",
          "widget_id": "viewport",
          "kind": "scroll_area",
          "props": {},
          "children": []
        }
      ]
    }
  }
}
```

### Example 2 — `patch_batch` frame with two patches

```json
{
  "t": "patch_batch",
  "v": 1,
  "s": "550e8400-e29b-41d4-a716-446655440000",
  "seq": 41,
  "payload": {
    "snapshot_revision": 7,
    "from_sequence": 41,
    "to_sequence": 42,
    "patches": [
      {
        "op": "update_prop",
        "id": "surf-1#root",
        "key": "title",
        "value": "Terminal — /home/user"
      },
      {
        "op": "update_layout",
        "id": "surf-1#root",
        "x": 120,
        "y": 80,
        "w": 800,
        "h": 600
      }
    ]
  }
}
```

Each patch is encoded with an `"op"` discriminator (snake_case) and a canonical `"id"` of the form `"<surface_id>#<widget_id>"`. Variants map to `PatchKind` in `src/lib/common/ui/patch.spl`: `insert_child`, `remove_child`, `replace_node`, `update_prop`, `remove_prop`, `update_layout` (fields `x`/`y`/`w`/`h`), `update_visibility`, `move_child`. `src/lib/common/ui/patch_wire.spl` is the canonical encoder.

### Example 3 — `input_event` frame

```json
{
  "t": "input_event",
  "v": 1,
  "s": "550e8400-e29b-41d4-a716-446655440000",
  "seq": null,
  "payload": {
    "surface_id": "surf-1",
    "widget_id": "viewport",
    "event": {
      "kind": "KeyDown",
      "key_code": 65,
      "modifiers": 0,
      "repeat": false
    }
  }
}
```

`event.kind` and its sub-fields are the variant names from `WmInputEvent` in `src/os/services/wm/window_protocol.spl`.

---

## 7. Versioning

- `protocol_version` starts at `1`.
- It mirrors the `protocol_version` field of `UiAccessSnapshot` in `src/lib/common/ui/access.spl`.
- The `hello` message carries `protocol_version` from the client.
- If the client's `protocol_version` differs from the server's supported version, the server sends:

```json
{
  "t": "error",
  "v": 1,
  "s": null,
  "seq": null,
  "payload": {
    "code": "VERSION_MISMATCH",
    "message": "Server supports protocol_version 1; client sent 2.",
    "retry_after_ms": 0
  }
}
```

and closes the WebSocket connection with close code 1002 (Protocol Error). The client must not retry without a software upgrade.

---

## 8. Reconnect Semantics

The client carries `(session_id, snapshot_revision, last_sequence)` across connections. On reconnect it sends `resume_session` with these values.

### Server decision logic

```
if snapshot_revision == current_revision
   AND last_sequence >= (current_sequence - retention_window):
     send patch_batch(from_sequence = last_sequence + 1)
     # patches retrieved via access_store.query_events(session_id, from: last_sequence + 1)
     # from src/lib/common/ui/access_store.spl
else:
     send snapshot(full UiAccessSnapshot, new revision)
     # client must discard all local state and rebuild from scratch
```

- `retention_window` is a server-side configuration constant (default: last 1 000 sequences). It is not negotiated on the wire in v1.
- `access_store.query_events` is defined in `src/lib/common/ui/access_store.spl` (SQLite-backed, existing).
- The revision counter lives in `PatchStream.snapshot_revision: u64` (`src/lib/common/ui/patch_stream.spl`, Phase 1). It is bumped on any structural reset (e.g., full re-render, session recreation) but not on every patch.

### Client obligations

- Persist `(session_id, snapshot_revision, last_applied_sequence)` in durable client storage between connections.
- On receiving a fresh `snapshot`, discard the previous `snapshot_revision` and update all three persisted values.
- Send `ack { last_applied_sequence }` after applying each `patch_batch` so the server can advance its GC watermark.

---

## 9. Backpressure

- The server maintains one `BoundedChannel` per client connection, implemented in `src/app/ui.web/bounded_channel.spl` (Phase 2 — new file). Default capacity: 256 slots. Policy: drop-oldest on overflow.
- When the channel overflows, the server closes the WebSocket with close code **1013** (Try Again Later) and, if the HTTP layer is still reachable, includes a `Retry-After` hint in the close reason string.
- The accept loop itself is never stalled by a slow client: the bounded channel absorbs burst writes; overflow silently drops the oldest queued frame and inserts the new one.
- The client is responsible for:
  1. Reconnecting after a 1013 close.
  2. Sending `ack { last_applied_sequence }` frequently enough that the server can GC the patch log and reduce queue depth. A client that never sends `ack` will exhaust the retention window and force a full `snapshot` on every reconnect.
- The unbounded channels at `src/app/ui.web/async_server.spl:68-69` are replaced with `BoundedChannel` in Phase 2.

---

## 10. Security Contract (MDSOC-Preserving)

This section enumerates all security invariants enforced by the protocol. Each invariant maps to an existing or forthcoming Simple component.

**1. Origin allowlist validated pre-upgrade.**
Before `compute_ws_accept` is called, `src/app/ui.web/origin_guard.spl` (Phase 2) reads the `Origin` (and, where present, `Referer`) HTTP header and verifies it against the server-side `SIMPLE_UI_WEB_ALLOWED_ORIGINS` environment variable. Any request whose origin is absent from the allowlist receives HTTP 403; the WebSocket upgrade never proceeds. This prevents cross-origin connection injection.

**2. Bearer token HMAC-bound to grant id, origin, and expiry.**
`/ui/login` calls `session_token.issue(grant)` from `src/app/ui.web/session_token.spl` (Phase 2). The token is a 32-byte value HMAC-signed over `(grant_id || origin || expiry_ms)` where `grant_id` comes from `src/lib/common/security/enforcement/capability.spl` (existing, untouched). `session_token.verify(token, origin)` is called during the WS upgrade, after origin validation but before `compute_ws_accept`. An expired, forged, or origin-mismatched token yields HTTP 403 and no 101 response.

**3. Per-event capability re-validation.**
Every inbound `input_event` and `window_cmd` is re-validated by `capability_policy.require_for_window(wid, cap)` in `src/lib/common/ui/capability_policy.spl` (extended in Phase 2). The required capability is: `InputInject` for `input_event`, `WindowCreate` / `WindowClose` / `WindowResize` / `WindowMove` for the corresponding `window_cmd` variants. Denial produces an `error` frame sent to the client and an audit log entry via the existing audit hook in `capability_policy.spl`. No silent drops.

**4. Client-asserted `window_id` never trusted.**
The `window_id` field present in `input_event` and `window_cmd` payloads is treated as an unverified hint. The server always resolves the authoritative `WindowId` through `UiWindowSurfaceRegistry.lookup(surface_id)` in `src/lib/common/ui/window_surface_registry.spl` (existing, untouched). If the client-supplied `window_id` does not match the registry result, the request is rejected with an `error` frame.

**5. TLS required; rustls via existing infrastructure.**
WSS connections must be TLS-encrypted. TLS is handled entirely by `rt_tls_server_create(port, cert, key)` in `src/lib/nogc_sync_mut/io/tls_ffi.spl` (existing rustls wrapper, untouched). No custom TLS code is introduced. The `--tls` CLI flag (added to `src/app/ui.web/server.spl` in Phase 2) activates this path. Plain WebSocket (`ws://`) is rejected in production mode.

---

## 11. Out of Scope for v1

The following items are listed as v2 roadmap and are explicitly excluded from this specification:

- **Binary / CBOR payload framing** — v1 uses JSON exclusively. CBOR or a custom binary encoding would reduce bandwidth for large `patch_batch` payloads but requires client-side CBOR support and is deferred.
- **WebTransport, QUIC, and raw native TCP transport** — v1 uses WSS only. Native (non-browser) adapters may use raw TCP in v2, sharing the same message semantics but bypassing WebSocket framing. WebTransport / QUIC integration is a separate v2 concern.

---

## Appendix A — Symbol Index

Quick reference for all external symbols cited in this document.

| Symbol | File |
|--------|------|
| `UiAccessSnapshot`, `UiAccessNode`, `UiAccessSurface`, `UiAccessEvent`, `sequence: i64` | `src/lib/common/ui/access.spl` |
| `UIPatch`, `PatchKind` | `src/lib/common/ui/patch.spl` |
| `access_store.query_events` | `src/lib/common/ui/access_store.spl` |
| `UiWindowSurfaceRegistry.lookup` | `src/lib/common/ui/window_surface_registry.spl` |
| `Capability`, `ClipboardRead`, `ClipboardWrite` | `src/lib/common/ui/capability.spl` |
| `capability_policy.require_for_window` | `src/lib/common/ui/capability_policy.spl` |
| `WmInputEvent`, `WmCreateRequest`, `WmCloseRequest`, `WmResizeRequest`, `WmMoveRequest`, `WmFocusEvent`, `Rect`, `WindowId` | `src/os/services/wm/window_protocol.spl` |
| `compute_ws_accept`, `send_ws_text`, `escape_json_string` | `src/app/ui.web/ws_handler.spl` |
| `parse_ws_event`, `extract_field` | `src/app/ui.web/async_ws.spl` |
| `rt_tls_server_create` | `src/lib/nogc_sync_mut/io/tls_ffi.spl` |
| `CapabilityPolicy` grant id, `expiry_ms` | `src/lib/common/security/enforcement/capability.spl` |
| `PatchEnvelope`, `encode_patch`, `decode_patch` | `src/lib/common/ui/patch_wire.spl` *(Phase 1 — new)* |
| `encode_snapshot`, `decode_snapshot` | `src/lib/common/ui/snapshot_wire.spl` *(Phase 1 — new)* |
| `PatchStream`, `snapshot_revision: u64`, `patches_since` | `src/lib/common/ui/patch_stream.spl` *(Phase 1 — new)* |
| `session_token.issue`, `session_token.verify` | `src/app/ui.web/session_token.spl` *(Phase 2 — new)* |
| `origin_guard.check` | `src/app/ui.web/origin_guard.spl` *(Phase 2 — new)* |
| `BoundedChannel` | `src/app/ui.web/bounded_channel.spl` *(Phase 2 — new)* |
| `ImeCompose` cap | `src/lib/common/ui/capability.spl` *(Phase 2 — extension)* |
| `SurfaceSubscribe`, `WindowCreate`, `InputInject` caps | `src/lib/common/ui/capability.spl` *(Phase 2 — extension)* |
| `require_for_surface`, `require_for_window` helpers | `src/lib/common/ui/capability_policy.spl` *(Phase 2 — extension)* |
