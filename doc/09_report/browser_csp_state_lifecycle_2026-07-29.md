# Browser CSP State Lifecycle

Status: OPEN security/evidence blocker

## Broker patch state

An uncommitted broker patch currently:

- derives bounded effective CSP from authenticated response headers and eligible
  head `<meta http-equiv="Content-Security-Policy">`;
- intersects newline- and comma-separated policy lists;
- enforces CSP before renderer-requested cookie writes, HSTS queuing, transport,
  handles, or response-body release;
- covers resource directives, fallback, redirects, 4xx/5xx documents, 304
  policy preservation, history bounds, and fail-closed missing metadata.

Independent source review passed those behaviors.

## Remaining acceptance blocker

The current site-swap test manually calls process `_csp_state()` and
`_load_csp_state()`, then separately checks decoder generations. It does not
drive the production `HostedBrowserRendererRegistry.advance_window` →
`_begin_site_swap` path.

Required evidence:

1. Start a registry-owned renderer with committed active/history CSP.
2. Trigger a cross-site navigation through `advance_window`.
3. Observe the production replacement generation and process identity.
4. Prove active/history CSP transfers and stale pending CSP does not.
5. Feed an old-generation SBRQ4 request and prove rejection by the replacement.

Do not close this row with source inspection or direct state-copy helpers.

## Separate BrowserSession defects

The in-process BrowserSession history path stores effective header+meta CSP,
then reparses and appends the same meta policy on back/forward/reload. Policy
memory can therefore grow across traversal. CSP bytes are not included in the
history byte budget, and parse failure/close can retain CSP and sandbox state.

Fix the canonical owner by separating base header policy from effective policy,
bounding/counting policy bytes, computing meta intersection once per document,
and clearing policy/sandbox state on failure and close.
