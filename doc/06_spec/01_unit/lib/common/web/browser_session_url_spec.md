# BrowserSession URL Boundary Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 5 | 5 | 0 | 0 |

## Scenarios

- Separate origin, host, hostname, query, fragment, and userinfo while rejecting
  credential-bearing navigation.
- Reject ASCII request-line control characters anywhere in a network URL.
- Reject empty, malformed, unroutable, and out-of-range authorities.
- Admit canonical HTTPS bracketed-IPv6 navigation literals only after structural
  URL-parser validation: `::` is unique, hex groups are bounded, eight address
  units are exact unless compressed, and an embedded IPv4 tail is valid and final.
  Reject malformed brackets, suffix injection, invalid literals, and invalid ports
  before the public transport boundary.
- Encode address-bar search text as one UTF-8 form query value.

Requirement trace (URL-admission portion): REQ-WEB-BROWSER-009,
REQ-WEB-BROWSER-010, REQ-WEB-BROWSER-011, REQ-WEB-BROWSER-015,
REQ-WEB-BROWSER-020.

Source: `test/01_unit/lib/common/web/browser_session_url_spec.spl`

Updated: 2026-07-30.

Docgen: pending — no deployed self-hosted runtime was available in this
isolated worktree; this manual is a reviewed mirror of the executable spec.
