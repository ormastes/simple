# Browser Sandbox Form Navigation Authorization

> A local typed HTTPS fixture proves that CSP sandbox `allow-forms` does not
> grant top-level form navigation, while the explicitly authorized POST path
> remains functional.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 1 | 1 | 0 | 0 |

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Requirement | `REQ-WEB-BROWSER-012` |
| Source | `test/03_system/security/browser_sandbox_form_navigation_authorization_spec.spl` |
| Evidence | Typed HTTPS/certificate fixture, exact request state, canonical Draw IR, literal full framebuffer |
| Provenance | Static/manual review of the committed executable SSpec; runtime PASS is unclaimed |

## Scenario

### should render only the document authorized for top navigation

1. **Resolve the HTTPS destination**
   - Start the typed browser navigation at
     `https://account.test/profile`.
   - Take the document request and require that exact canonical HTTPS URL.

2. **Validate the authenticated peer**
   - Validate the typed `account.test` certificate fixture against the local
     `ISRG Root X1` trust-anchor fixture.
   - Commit an injected HTTPS response with
     `Content-Security-Policy: sandbox allow-forms` and a collector POST form.
   - Capture the committed URL and HTML body.
   - Require the `authorized` Draw IR command to have kind `rect`, component
     `authorized`, parent `surface`, box `(0,0,8,4)`, present clip
     `(0,0,8,4)`, and color `0xFF2563EB`.
   - Require the complete 8-by-4 framebuffer to be the literal array of 32
     `0xFF2563EB` pixels.

3. **Apply redirect and sandbox policy**
   - Require `allow_forms=true` and `allow_top_navigation=false`.
   - Click the denied form submit button and require exactly zero pending
     requests, no request/body value, and the exact warning array
     `["CSP sandbox blocked top navigation"]`.
   - Load the positive control with
     `sandbox allow-forms allow-top-navigation`.
   - Require its exact authorized request to be
     `POST https://account.test/save` with body `name=Ada`.

4. **Render only the authorized response**
   - Require the denied session URL and HTML body to remain byte-for-byte
     unchanged.
   - Require the full serialized `DrawIrComposition` to remain unchanged.
   - Recheck the absolute `rect` / `authorized` / `surface` identity, box,
     present clip, and `0xFF2563EB` color.
   - Recheck the complete framebuffer against the literal 32-pixel blue
     oracle rather than comparing the renderer only to itself.

## Pass/Fail Oracle

PASS requires the denied collector request and `token-123` body never to enter
the pending queue; the exact warning array, URL, HTML, Draw IR, and complete
framebuffer must remain fixed; and the explicitly authorized `/save` POST must
retain its exact method and body. Any queued denied request, document or render
mutation, warning drift, or positive-control mismatch is FAIL.

## Companion Integration Controls

`test/02_integration/rendering/browser_session_dom_input_spec.spl` exercises
both button-click and implicit-Enter denial with `sandbox allow-forms`, plus
button and keyboard positive controls with
`sandbox allow-forms allow-top-navigation`.

<details>
<summary>Executable SSpec</summary>

The complete executable source, including the literal 32-pixel framebuffer
oracle and all direct assertions, is maintained at
`test/03_system/security/browser_sandbox_form_navigation_authorization_spec.spl`.

</details>
