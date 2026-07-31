# CORS Request-Header Preflight Test Plan

## Scope

This lane proves that non-safelisted author headers use the existing
`FetchEngine.handle_cors_preflight` OPTIONS path before actual transport.
Cookie-name validation, TLS verification, mixed content, HSTS, HTTP framing,
preflight caching, and response-header exposure are excluded.

## Execution and evidence

The visible system flow is frozen to four steps:

1. `Register a cross-origin endpoint that omits X-Admin-Action permission`.
2. `Issue a credential-free CORS GET carrying X-Admin-Action`.
3. `Observe the first and only OPTIONS advertising x-admin-action`.
4. `Reject the fetch before the ungranted action reaches the endpoint`.

Protocol evidence is authoritative: one matching request, method `OPTIONS`,
exact lowercase ACRH token, zero matching `GET` requests, and a typed preflight
denial. Focused unit matrices additionally cover the 128-byte per-value and
1,024/1,025 aggregate boundaries in UTF-8 bytes, aggregate escalation of
`Range`, ordered/open versus reversed/suffix/multiple ranges, duplicate-name
comma-space normalization before classification, safelisted methods without
ACAM, ACAM `*` with omitted and included credentials, ordinary ACAH wildcard
behavior, and explicit `Authorization` permission.

## Pass/fail criteria

Any actual GET before a successful header grant is FAIL. Missing or unsorted
ACRH names, wildcard authorization, a credentialed wildcard method/header
grant, codepoint-counted limits, a reversed safelisted Range, or preflight at
exactly 1,024 safe value bytes is FAIL. A noncredentialed custom header may use
ACAH `*`; `Authorization` may not.

Runtime execution is not authorized in this lane, so source/static completion
does not constitute runtime or SPipe PASS.

## Traceability

| Requirement | Executable evidence | Manual | Coverage |
|---|---|---|---|
| REQ-WEB-BROWSER-010 | `test/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.spl`; `test/01_unit/browser_engine/net/cors_spec.spl` | `doc/06_spec/03_system/security/browser_fetch_cors_unsafe_header_preflight_spec.md` | OPTIONS/ACRH/no-GET plus policy matrix; runtime pending |
| REQ-WEB-BROWSER-012 | focused system denial scenario | same | Side effect blocked before actual transport; runtime pending |
| REQ-WEB-BROWSER-021 | modern four-step SSpec | same | Mirrored artifact pair; runtime pending |
