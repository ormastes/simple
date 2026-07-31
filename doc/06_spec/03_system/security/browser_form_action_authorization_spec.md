# Browser Form-Action Authorization

> An authenticated HTTPS document keeps live form data inside its committed
> CSP capability and preserves the authorized rendered surface after denial.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Requirement | `REQ-WEB-BROWSER-012` |
| Source | `test/03_system/security/browser_form_action_authorization_spec.spl` |
| Evidence | HTML, exact Draw IR geometry/source, full framebuffer, request envelope |

## Scenario

### should keep form data and rendering inside the authorized origin

1. **Establish the authenticated navigation**
   - Commit an HTTPS account document with a secure session cookie.
   - Show the visible `Authorized profile` surface and its live form value.

2. **Apply origin and sandbox policy**
   - Confirm the response CSP permits form mechanics and same-origin state.
   - Confirm `form-action 'none'` remains the destination authority.
   - Require the WebIR-derived `DrawIrComposition` batch's complete source
     metadata to identify the HTML AST owner and the stable `authorized`
     command to occupy `(0,0,8,4)`.
   - Require all 32 framebuffer pixels to equal the fixed blue ARGB oracle.

3. **Reject invalid transport or capability state**
   - Activate the cross-origin POST form through implicit Enter submission.
   - Resolve the dispatched typed route back to the indexed `send` author ID.
   - Require a CSP denial warning, zero queued requests, and no queued body.
   - Separately resolve the `save` route and prove `form-action 'self'` queues
     the authorized same-origin POST with its exact live body.

4. **Render only the authorized document**
   - Keep the HTTPS account URL and visible profile document committed.
   - Recheck exact command geometry, source identity, color, and all 32 pixels
     against fixed values rather than comparing the renderer to itself.

## Pass/Fail Oracle

PASS requires the denied destination and `token-123` body never to enter a
pending request, the same-origin `/save` POST to remain functional, and the
authorized document's canonical command and complete framebuffer to match the
fixed oracle. Author IDs are evidence projections from generation-qualified
dispatch routes, never dispatch authority. Any cross-origin queued request,
document replacement, geometry or source mismatch, or pixel mismatch is FAIL.

## Companion Integration Controls

The focused browser-session integration spec additionally fixes the CSP
source-list boundary: scheme-less and wildcard hosts, default/explicit/wildcard
ports, path matching, HTTP-to-HTTPS scheme upgrades, downgrade rejection, and
malformed host sources. Its redirect chain also proves that a denied target is
authorized before `Set-Cookie` or `Strict-Transport-Security` can change state,
while the current URL, HTML, and pending-request queue remain unchanged.

<details>
<summary>Executable SSpec</summary>

The complete executable source is maintained at
`test/03_system/security/browser_form_action_authorization_spec.spl`.

</details>
