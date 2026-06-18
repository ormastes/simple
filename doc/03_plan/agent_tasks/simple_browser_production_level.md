# Simple Browser Production Level Agent Task Plan

## Objective

Make the Simple browser production-ready as a whole feature, not only as an
endpoint-hardening lane.

## Agent Team Results

- Security explorer found hidden production gaps in login authorization, token
  lifecycle, production defaults, CSRF/Host/Sec-Fetch policy, rate limiting,
  headers, WebSocket validation, logging redaction, and async-server parity.
- Visible-feature explorer found gaps in navigation, durable restore, offline
  state, accessibility, and whole-browser requirements.
- Renderer/platform explorer confirmed external native readback remains blocked
  by unavailable hosts and found local generated-manual/manifest-validation
  follow-up work.

## Work Plan

1. Security local slice: harden WebSocket handshake validation for version and
   key shape across normal, TLS, async, and `/ui/ws` route paths.
2. Requirements selection: user selects feature/NFR option A, B, or C from the
   option docs before final requirements are written.
3. Security program: implement real login authorization, token lifecycle,
   production bind/default-origin posture, CSRF/Host/Sec-Fetch checks,
   per-principal limits, and redacted security logging.
4. UX program: implement navigation model, durable restore, visible degraded
   state, accessibility/keyboard evidence, and workflow docs.
5. Renderer/platform program: generate missing mirrored manuals, add manifest
   acceptance validation, and keep external native readback gates open until
   accepted host evidence exists.
6. Verification: run focused checks once per slice, regenerate SSpec manuals,
   and keep `doc/06_spec` free of executable `.spl` specs.

## Current Implementation Status

- Done: WebSocket handshake version/key-shape gate with focused unit coverage.
- Done: Visible degraded-mode shell evidence now includes accessible status,
  retry count/delay metadata, capped reconnect backoff, and a manual reconnect
  action in both the normal Simple Web shell and shared compact web-render
  wrapper.
- Done: Durable reconnect now persists the Simple Web `snapshot_revision` and
  `last_sequence` cursor in browser storage and sends `resume_session` on
  reconnect before falling back to a fresh `open_session`.
- Done: Browser navigation intent contract now exposes hidden accessible
  back/forward/reload/address controls and sends stable `browser_navigation`
  events for host chrome wiring.
- Done: Browser navigation is now represented in the shared backend event
  model as `UIEvent.BrowserNavigation(action, url)`, serialized through the
  common web-render input envelope, recorded by UI session dispatch, and
  parsed by Simple Web/TUI-web/direct IPC paths behind explicit action
  allowlists.
- Pending: final option selection for the broader feature/NFR scope.
- Pending: external-host Metal/ROCm/HIP/DirectX/WebGPU `device_readback`
  evidence remains required before renderer/platform gates can close.
