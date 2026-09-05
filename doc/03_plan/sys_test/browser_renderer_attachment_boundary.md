# Browser renderer attachment boundary test plan

## Scope

Verify that a top-level HTTP response with any case-insensitive
`Content-Disposition: attachment` disposition token is rejected before hosted
parent document staging or SBR2 response-body forwarding, and independently
before `BrowserSession` commits HTML. A download subsystem is excluded.

## Scenario and evidence

The modern four-step scenario is executable at
`test/03_system/security/browser_renderer_attachment_boundary_spec.spl` and
mirrored at
`doc/06_spec/03_system/security/browser_renderer_attachment_boundary_spec.md`.
Protocol evidence is selected; runtime capture remains pending because this
change is restricted to static guards.

## Traceability

| Requirement | Coverage |
|---|---|
| REQ-WEB-BROWSER-005 | Host navigation retains the committed page |
| REQ-WEB-BROWSER-010 | Parent broker owns attachment classification |
| REQ-WEB-BROWSER-012 | Hostile attachment HTML receives no activation |
| REQ-WEB-BROWSER-021 | SBR2 body/frame authority remains unchanged |

## Pass criteria

- Mixed-case, OWS-padded, parameterized attachment values are recognized.
- A later attachment value among duplicate Content-Disposition fields wins.
- Inline or absent disposition is not classified as an attachment.
- URL, history, CSP, DOM/body, global, cookie, and frame witnesses are unchanged.
- Parent pending commit/origin/CSP fields and SBR2 response body remain empty.
- Both guards return `document-attachment-unsupported`.
