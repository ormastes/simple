# Electron keyboard input drops all modifier state and most non-printable keys

## Status
Open.

## Severity
Medium — functional gap; duplicated logic is also a code-reuse smell.

## Summary
`src/app/ui.electron/preload.js:25-33` and `bridge.js:631-636` (internal MDI windows) use identical hardcoded allowlist: `event.key.length === 1 || ['Enter','Escape','Backspace','Tab','ArrowUp','ArrowDown','ArrowLeft','ArrowRight']`. No `ctrlKey`/`metaKey`/`altKey`/`shiftKey` state is read, and wire protocol (`ui.ipc/protocol.spl:86-96`) has no modifier field.

## Evidence
- **preload.js:25-33**: Allowlist is `length==1 || named_keys` with no modifier read.
- **bridge.js:631-636**: Identical allowlist in MDI window binding.
- **protocol.spl:86-96**: `"keypress"`/`"input"` messages carry only bare `key` string, no modifiers.
- Keys like Delete, Home, End, F1-F12, or Ctrl/Cmd combos (e.g. Ctrl+A) either dropped outright or sent as bare key.

## Failure Scenario
Any app-level keyboard shortcut bound to modifier combo or non-whitelisted special key is unusable in Electron lane (both plain and MDI windows). Ctrl+A misfires as bare `a`.

## Related Issue (M7)
`ui.ipc/protocol.spl:289-310` defines `build_ipc_request_fetch` / `build_ipc_request_http` with documented reply via `fetch_result` message (parsed at lines 248-259 into `UIEvent.FetchResult`). However, `src/app/ui.electron/bridge.js` has no handler for `msg.type === 'request_fetch'`. Same for `paint_canvas`, `moveWindow`, `resizeWindow`, `focusWindow`, `minimizeWindow`, `surfaceState` — all defined as `build_ipc_*` but unhandled in bridge.js. Currently dormant since nothing calls these builders, but any future caller will block forever waiting for a response that bridge.js never produces.

## Next Step
Add modifier-field to protocol; read and forward `ctrlKey`/`metaKey`/`altKey`/`shiftKey`; consolidate duplicated allowlist. Separately: implement missing `request_fetch` and other round-trip handlers in bridge.js (currently latent traps).
