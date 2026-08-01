# BrowserSession script-navigation reference security

Location and History API navigation share one strict URL-reference policy.
Address-bar search fallback is not part of this path.

## Share strict scheme and reference policy across location and history

1. Commit equivalent stable HTTPS documents for rejected, valid-reference, and
   History API controls.
2. Attempt opaque and unknown schemes through `location.assign()`,
   `history.pushState()`, and `history.replaceState()`, plus explicit and
   network-path cross-origin History URLs.
3. Verify URL, document, title, body, history/index, navigation proposals,
   runtime location and history state, warnings, and network/loading state
   remain unchanged.
4. Verify bare, root, dot, parent, query, fragment, HTTPS network-path, and
   explicit HTTPS Location references; then verify same-origin History push,
   replace, back, and forward traversal with exact URLs.

The executable scenario uses direct state, history, runtime, proposal, and
network matchers for every admitted or rejected transition.
