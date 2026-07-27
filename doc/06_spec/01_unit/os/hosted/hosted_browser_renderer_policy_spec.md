# Hosted Browser Renderer Broker Policy Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 21 | 21 | 0 | 0 |

## Covered boundaries

- Issue and consume one bounded canonical HTTP(S) navigation permit.
- Load persisted HSTS and rewrite trusted navigation and redirect targets.
- Learn HSTS from authenticated HTTPS before status or CORS exposure, while
  ignoring STS delivered over plaintext HTTP or synthetic HTTPS responses
  without transport-authentication provenance.
- Bound response bodies before Wasm hex expansion.
- Preserve renderer readiness, Stop, Reload, input, animation, and network
  request ordering.
- Retain a failed native process-close handle for bounded hosted-WM shutdown
  retry, but clear handles already reaped by a liveness check.
- Derive same-origin, CORS, mixed-content, and preflight policy from trusted
  broker state rather than renderer-supplied request kinds.

Requirement trace: REQ-WEB-BROWSER-011, REQ-WEB-BROWSER-017,
REQ-WEB-BROWSER-018.

Source:
`test/01_unit/os/hosted/hosted_browser_renderer_policy_spec.spl`

Updated: 2026-07-27.
