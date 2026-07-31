# Hosted Browser CORS Preflight

Proves the sandbox broker runs a public-only OPTIONS job before an unsafe
cross-origin request and never publishes preflight authority or side effects.

Requirements: `REQ-WEB-BROWSER-010`, `REQ-WEB-BROWSER-012`,
`REQ-WEB-BROWSER-021`.

## Scenario: Publish only an actual request admitted by OPTIONS

1. **Admit the hosted unsafe request**
   - Submit a credential-free cross-origin POST with `X-Admin-Action`.
   - The broker admits CORS mode, retains sanitized author headers, and leaves
     `Origin` generation to FetchEngine.

2. **Run OPTIONS before the actual request**
   - Observe exactly one OPTIONS request followed by exactly one POST.
   - OPTIONS carries the requester origin, requested method, and sorted
     `content-type, x-admin-action` header names without cookies.

3. **Cancel denied preflight work without side effects**
   - A redirected or ungranted OPTIONS response produces one CORS denial and
     zero actual requests.
   - Stop clears the staged phase and actual request. Preflight cookies, HSTS,
     cache, redirects, and response bodies remain unobservable.

4. **Publish only the validated actual response**
   - The renderer receives the validated actual status through its bound
     response wire.
   - `Set-Cookie` and `Strict-Transport-Security` are not exposed to renderer
     content, and mock/preflight traffic does not seed HSTS.

Executable source:
`test/03_system/security/browser_hosted_cors_preflight_spec.spl`.
