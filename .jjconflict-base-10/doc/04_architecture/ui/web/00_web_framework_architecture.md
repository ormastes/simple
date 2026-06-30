# Web Framework Architecture

This is the entrypoint for web framework architecture as it connects to the UI
stack. It covers the app/web-framework lane, the `ui.web` protocol lane, and
the verification sample that keeps both grounded.

## Scope

The web framework owns HTTP routing, auth/session, request handling,
persistence adapters, and web-app composition. The UI stack owns semantic UI
state, snapshots, patches, input events, and host-window commands. The
connection point is `ui.web`: a Simple-owned session protocol that transports UI
snapshots and patch batches to browser or native web shells.

## Connected Flow

```text
Web route / app action
  -> app model + session store
  -> Simple UI state update
  -> UiAccessSnapshot / UIPatch
  -> ui.web WebSocket protocol
  -> browser / Electron / SimpleWeb adapter
  -> input_event / window_cmd back to Simple
```

## Ownership Split

| Concern | Owner |
|---------|-------|
| Routes, forms, auth/session | Web framework app layer |
| Persistence | `WebRecordStore<T>`, SQLite, SimpleDB adapters |
| UI session state | Simple UI runtime |
| Snapshot/patch transport | `ui.web` protocol |
| Browser/Electron host effects | Thin adapter only |
| `/api/test/*` routes | UI test API, unchanged by `ui.web` |

## Invariants

- Browser, Electron, and SimpleWeb adapters are thin endpoints. They must not
  become the application runtime.
- `ui.web` is connected to the UI architecture through `UiAccessSnapshot`,
  `UIPatch`, and shared surface ids.
- `/api/test/*` stays bit-compatible with the UI test API and is not replaced by
  the session WebSocket protocol.
- Persistence/session tests should use the canonical web stack sample when they
  need end-to-end web framework evidence.

## Detailed Docs

- `../ui_web_protocol.md`
- `web_stack_sample.md`
- `html_css_binary_caching.md`
- `web_db_primitive_hardening.md`
- `../00_ui_architecture.md`

