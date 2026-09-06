# Browser Form-Action Authorization — System Test Plan

## Scope

Prove that `BrowserSession` applies response-header CSP `form-action` to the
fully resolved form destination before queuing a document request. Preserve the
existing sandbox, form serialization, WebIR, Draw IR, and Engine2D paths.
Exercise scheme-less and wildcard host sources, scheme upgrades without
downgrades, default/explicit/wildcard ports, malformed host sources, and carry
the initiating policy through every document redirect.

Excluded: live public network traffic, certificate-provider acceptance, redirect
transport execution, iframe browsing contexts, and compiler/bootstrap work.

## Execution

1. Run the focused integration spec:
   `test/02_integration/rendering/browser_session_dom_input_spec.spl`.
2. Run the system scenario:
   `test/03_system/security/browser_form_action_authorization_spec.spl`.
3. Generate the mirrored manual with pure-Simple `spipe-docgen`; a Rust seed is
   not acceptable evidence.

## Pass Criteria

- `form-action 'none'` queues no request and exposes no POST body.
- `form-action 'self'` permits the resolved same-origin POST.
- Absent `form-action` does not inherit `default-src`.
- Scheme-less hosts, wildcard subdomains, default/explicit/wildcard ports, and
  source paths match in the shared CSP source-list owner; malformed host/port
  sources fail closed and fetch-directive `default-src` fallback is unchanged.
- An `http:` scheme source permits the CSP-defined HTTPS upgrade while an
  `https:` source rejects an HTTP downgrade.
- The initiating policy and protected-document URL survive allowed redirects;
  a later disallowed target is rejected before response cookies, HSTS state,
  current document state, or the pending request queue can change.
- Click, implicit Enter, and keyboard button activation share the same
  deny-before-queue form submission gate.
- Denial preserves current URL and visible HTML; canonical command geometry,
  batch source, and the complete framebuffer equal fixed external oracles.
- No raw URL parser, `rt_*` call, alternate renderer, or protocol bypass exists.

## Traceability

| Requirement | Executable coverage | Cases | Evidence |
|-------------|---------------------|-------|----------|
| REQ-WEB-BROWSER-012 | `test/02_integration/rendering/browser_session_dom_input_spec.spl` | none/self/absent, host/scheme/port grammar, redirect chain, implicit/keyboard | request policy/origin, URL, method, body, denial warning, cookie/HSTS/document immutability |
| REQ-WEB-BROWSER-012 | `test/03_system/security/browser_form_action_authorization_spec.spl` | deny/allow/render preservation | HTML, exact Draw IR geometry/source, full framebuffer |

The mirrored operator manual is
`doc/06_spec/03_system/security/browser_form_action_authorization_spec.md`.
