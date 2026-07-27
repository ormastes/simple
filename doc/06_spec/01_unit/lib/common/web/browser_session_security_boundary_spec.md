# BrowserSession Security Boundary Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 20 | 20 | 0 | 0 |

## Covered boundaries

- Reject direct file, executable, data, and unknown navigation schemes.
- Reject request-line control characters again at the central subresource
  request pump without echoing hostile URL text into diagnostics.
- Block mixed-content and unvalidated cross-origin executable resources.
- Allow explicitly registered HTTPS resources without filesystem access.
- Escape page-controlled title markup before rendering.
- Reject mismatched response URLs and cross-origin fetch/redirects.
- Keep cookie and Web Storage authority on the committed document when script
  writes a cross-origin `location`, and reject cross-origin History API URLs.
- Permit same-origin fetch within request limits.
- Keep HttpOnly/transport cookie state outside page-visible JavaScript.
- Enforce document CSP before inline/external style, JavaScript, Simple Script,
  module/Wasm, and fetch dispatch.
- Recheck CSP on every normalized/HSTS-upgraded style, script, module, Wasm,
  and fetch redirect target before queuing another request.
- Upgrade HSTS hosts and included subdomains until deterministic max-age
  expiry.
- Restore only valid, unexpired, unique HSTS policies from wall-clock profile
  state, rejecting public suffixes and IP literals.
- Bound recursive Promise microtask work to eight 1000-callback batches per
  browser flush so hostile chains yield to the host.

## CSP scenario

The document response supplies:

```text
style-src 'none'; style-src *; script-src 'unsafe-inline'; connect-src *
connect-src 'none'
```

The executable scenario requires the allowed inline script to update the title,
while inline/external styles, the external script, and same-origin fetch are
blocked before network dispatch. The session must expose typed `CSP blocked`
warnings and retain no stylesheet output. The duplicate `style-src` proves the
first directive wins; the second CSP header proves all policies are enforced.
The redirect scenario starts same-origin stylesheet and script requests under
`style-src 'self'; script-src 'self'`, redirects both to a hostile origin, and
requires explicit CSP errors with no redirected request.

Requirement trace: REQ-WEB-BROWSER-010, REQ-WEB-BROWSER-012,
REQ-WEB-BROWSER-013, REQ-WEB-BROWSER-015, REQ-WEB-BROWSER-017.

Source:
`test/01_unit/lib/common/web/browser_session_security_boundary_spec.spl`

Updated: 2026-07-27.
