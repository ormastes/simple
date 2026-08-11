# BrowserSession Redirect Security

Only top-level document downgrade policy uses the canonical scheme of the
matched inflight request. Active-subresource and fetch redirects are rechecked
against the secure client context and target trustworthiness. Fetch scenarios
enable `broker_network_policy` to model the trusted transport boundary. A
rejected redirect leaves the already committed page and history intact, while
loopback and HTTPS targets remain trustworthy.

Executable specification:
`test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl`

## Scenarios

### Reject a loopback stylesheet redirect to ordinary HTTP without replacing committed state

1. Commit two stable HTTPS pages, with the second requesting a loopback
   stylesheet.
2. Take and verify the allowed loopback stylesheet request.
3. Return a redirect from loopback to an ordinary HTTP stylesheet.
4. Require no pending request, a mixed-content warning, and exact preservation
   of URL, title, body, back target, and forward availability.

### Reject a loopback fetch redirect to ordinary HTTP without replacing committed state

1. Commit two stable HTTPS pages, with the second starting a loopback fetch.
2. Take and verify the allowed loopback fetch request.
3. Return a redirect from loopback to an ordinary HTTP resource.
4. Require fetch rejection, no pending request, and exact preservation of URL,
   title, body, back target, and forward availability.

### Continue following a brokered loopback fetch redirect to loopback

1. Open a secure page that starts a loopback fetch through the trusted broker
   transport boundary.
2. Take the allowed loopback fetch request.
3. Redirect it to another loopback URL.
4. Require the trustworthy loopback target to be scheduled unchanged.

### Continue following a loopback stylesheet redirect to loopback

1. Open a secure page that requests a loopback stylesheet.
2. Take the allowed loopback stylesheet request.
3. Redirect it to another loopback URL.
4. Require the trustworthy loopback target to be scheduled unchanged.

### Continue following a loopback stylesheet redirect to HTTPS

1. Open a secure page that requests a loopback stylesheet.
2. Take the allowed loopback stylesheet request.
3. Redirect it to an HTTPS URL.
4. Require the secure target to be scheduled unchanged.

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
