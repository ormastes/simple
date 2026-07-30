# BrowserSession Redirect Source-Scheme Security

The response URL is broker input. Redirect downgrade decisions use the
canonical URL of the matched inflight request, and a rejected document
redirect leaves the already committed page and history intact.

Executable specification:
`test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl`

## Scenarios

### Reject a case-variant document downgrade without replacing committed state

1. Commit two stable HTTPS pages to establish visible page and back-history
   state.
2. Start and take a secure document request.
3. Return the matching URL with an uppercase `HTTPS://` scheme and an HTTP
   redirect target.
4. Require an HTTPS-downgrade error, no pending load, and exact preservation of
   URL, title, body, back target, and forward availability.

### Reject a case-variant fetch downgrade

1. Open a secure page that starts a same-origin fetch.
2. Take the secure fetch request.
3. Return its matching URL with an uppercase `HTTPS://` scheme and an HTTP
   redirect target.
4. Require fetch rejection and no scheduled HTTP request.

### Reject a case-variant stylesheet downgrade

1. Open a secure page that requests a stylesheet.
2. Take the secure stylesheet request.
3. Return its matching URL with an uppercase `HTTPS://` scheme and an HTTP
   redirect target.
4. Require the downgrade warning and no scheduled HTTP request.

### Continue following an HTTPS redirect

1. Start an ordinary secure document navigation.
2. Take the secure document request.
3. Return its matching case-variant URL with another HTTPS URL as the target.
4. Require the unchanged secure target to be scheduled.

<details>
<summary>Executable SSpec</summary>

The complete runnable source is maintained at the executable specification
path above. It uses `std.spec.*`, `describe`, `it`, four visible `step(...)`
calls per scenario, direct assertions, and built-in matchers only.

</details>
