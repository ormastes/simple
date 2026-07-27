# Hosted Browser Renderer Broker Policy Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 23 | 23 | 0 | 0 |

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
- Convert persisted HSTS subresource upgrades into broker-owned internal
  redirects, accept only exact HTTP-to-HTTPS transport transforms, and strip
  STS before renderer delivery so unauthenticated responses cannot seed policy.
- Preserve request correlation, fetch method/body/headers, and the HTTP redirect
  budget across internal style, script, module, Wasm, and fetch upgrades;
  recompute Secure cookies for HTTPS and retain CSP denial on plain HTTP pages.
- Keep credential-free CORS responses from storing cookies or exposing
  non-safelisted, non-explicitly-exposed response headers to page code.

Requirement trace: REQ-WEB-BROWSER-011, REQ-WEB-BROWSER-017,
REQ-WEB-BROWSER-018.

Source:
`test/01_unit/os/hosted/hosted_browser_renderer_policy_spec.spl`

Updated: 2026-07-27.
