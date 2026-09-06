# Browser Sandbox Form Navigation Authorization Test Plan

## Scope

Verify REQ-WEB-BROWSER-012 for local typed HTTPS response fixtures: sandbox
`allow-forms` does not authorize top-level form navigation, while
`allow-forms allow-top-navigation` preserves exact POST behavior. Wire TLS,
HSTS, protocol runtime, and previously landed `form-action` behavior are out of
scope.

## Execution and pass criteria

1. Run `test/02_integration/rendering/browser_session_dom_input_spec.spl` in
   interpreter mode. Button and implicit-Enter denial must queue no request;
   the positive controls must queue the exact expected POST.
2. Run
   `test/03_system/security/browser_sandbox_form_navigation_authorization_spec.spl`.
   Its visible manual flow is: `Resolve the HTTPS destination`; `Validate the
   authenticated peer`; `Apply redirect and sandbox policy`; `Render only the
   authorized response`.
3. Review the static/manual-provenance scenario at
   `doc/06_spec/03_system/security/browser_sandbox_form_navigation_authorization_spec.md`.
   Regenerate it only when the pure-Simple runner/docgen lane is available.
   The scenario passes only when URL and body remain unchanged, serialized
   Draw IR is exactly equal, all final pixels are exactly equal, the canonical
   warning is present, and the positive request is the exact POST.

## Traceability

| REQ | Behavior | Executable coverage | Manual | Coverage |
|---|---|---|---|---|
| REQ-WEB-BROWSER-012 | CSP sandbox independently gates forms and top navigation | `test/02_integration/rendering/browser_session_dom_input_spec.spl`; `test/03_system/security/browser_sandbox_form_navigation_authorization_spec.spl` | `doc/06_spec/03_system/security/browser_sandbox_form_navigation_authorization_spec.md` | Button denial, keyboard denial, button allow, keyboard allow, exact render stability |

## Evidence and risks

The system scenario captures HTML-visible state and asserts canonical WebIR to
Draw IR plus complete pixel arrays. It uses no external network state. The main
risk is accidentally applying the sandbox gate to browser-chrome/address-bar
navigation; the fix therefore remains inside the DOM form submission owner.
