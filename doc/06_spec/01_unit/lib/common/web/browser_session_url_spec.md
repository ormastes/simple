# BrowserSession URL Boundary Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 4 | 4 | 0 | 0 |

## Scenarios

- Separate origin, host, hostname, query, fragment, and userinfo while rejecting
  credential-bearing navigation.
- Reject ASCII request-line control characters anywhere in a network URL.
- Reject empty, malformed, unroutable, and out-of-range authorities.
- Encode address-bar search text as one UTF-8 form query value.

Requirement trace: REQ-WEB-BROWSER-009, REQ-WEB-BROWSER-010,
REQ-WEB-BROWSER-015, REQ-WEB-BROWSER-020.

Source: `test/01_unit/lib/common/web/browser_session_url_spec.spl`

Updated: 2026-07-26.
