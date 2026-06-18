# Simple Browser Production Level Local Research

## Scope

This research covers the broader request to make the Simple browser production
level as a whole feature, including hidden security behavior that is not visible
in the UI.

## Current Evidence

- Existing production hardening covers token secret policy, origin-bound bearer
  checks, sensitive `/api/*` authorization, `/ui/resume`, `/ui/ws`, legacy `/ws`
  hiding, query-token non-authorization, bounded request/body/frame helpers,
  security headers, renderer parity, and local GPU evidence.
- The previous hardening lane remains `WARN`, not release-complete, because
  native Metal, ROCm/HIP, DirectX, and browser WebGPU `device_readback` proof
  require external hosts.
- Current requirements are security and renderer-hardening focused. They do not
  fully specify whole-browser production UX such as durable navigation state,
  reload/restart restore, offline/degraded UI, accessibility/keyboard operation,
  or end-user workflow documentation.

## Agent Team Findings

- Hidden security gaps: `/ui/login` still mints from a client-supplied grant,
  token lifecycle lacks revocation/rotation/session replay controls, production
  bind/default-origin posture is too permissive, CSRF/Host/Sec-Fetch coverage is
  incomplete, rate limiting is coarse, CSP permits inline scripts, WebSocket
  frame/handshake validation is partial, and logging redaction is not centralized.
- Visible feature gaps: navigation/back/forward/reload and address-entry flows
  are not production-proven, restore is reconnect-oriented rather than durable
  process-restart restore, offline/failure state is mostly console/retry, and
  accessibility evidence is static rather than live keyboard/screen-reader proof.
- Renderer/platform gaps: local Linux evidence is bounded correctly, but five
  GPU/platform specs need mirrored `doc/06_spec` manuals and external-host
  manifests must be validated before closing native readback gates.

## First Local Slice Implemented

The initial hidden-security slice hardens WebSocket handshakes by requiring
`Sec-WebSocket-Version: 13` and a nonce-shaped `Sec-WebSocket-Key` before any
normal, TLS, async, or `/ui/ws` route upgrade computes `Sec-WebSocket-Accept`.
