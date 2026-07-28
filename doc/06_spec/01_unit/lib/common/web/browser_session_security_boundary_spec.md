# BrowserSession Security Boundary Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 25 | 25 | 0 | 0 |

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
- Enforce path components on CSP HTTP(S) host sources, including uppercase
  schemes, exact paths, slash-terminated subtrees, and intentional root-origin
  access without widening narrower sources.
- Normalize validated explicit HTTP HSTS hosts and included subdomains until
  deterministic max-age expiry, mapping port 80 to HTTPS 443 while preserving
  other explicit ports and leaving malformed/non-HTTP inputs unchanged.
- Ignore malformed signed HSTS `max-age` directives without clearing an
  already valid policy while retaining `max-age=0` as explicit removal.
- Restore only strict DNS-host, unexpired, unique HSTS policies from wall-clock
  profile state, rejecting whitespace, userinfo, ports, malformed labels,
  public suffixes, and IP literals.
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
The host-source path scenario blocks `https://cdn.test/evil.js` under
`script-src https://cdn.test/allowed/` while dispatching
`https://cdn.test/allowed/app.js`.

Requirement trace: REQ-WEB-BROWSER-010, REQ-WEB-BROWSER-012,
REQ-WEB-BROWSER-013, REQ-WEB-BROWSER-015, REQ-WEB-BROWSER-017.

Source:
`test/01_unit/lib/common/web/browser_session_security_boundary_spec.spl`

Updated: 2026-07-27.
