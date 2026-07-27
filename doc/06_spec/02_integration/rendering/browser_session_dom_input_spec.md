# BrowserSession Live DOM Input Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 9 | 9 | 0 | 0 |

## Scenarios

- Checkbox click pre-activation is visible to the click handler, followed by
  bubbling `input` then `change`.
- A canceled checkbox click restores its prior checked state and emits neither
  `input` nor `change`.
- Link, button, form, keyboard, and stable-node-identity default actions route
  through BrowserSession.

Requirement trace: REQ-WEB-BROWSER-005, REQ-WEB-BROWSER-006.

Source: `test/02_integration/rendering/browser_session_dom_input_spec.spl`

Updated: 2026-07-26.
