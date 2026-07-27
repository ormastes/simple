# Browser Profile Store Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

The hosted browser profile owner writes versioned SQLite bookmark and HSTS
state, closes it, reopens the same profile, rejects corrupt file-scheme,
public-suffix, userinfo, port-bearing, and malformed DNS-host records, and
case-folded duplicate HSTS records, and proves removal remains durable after
another reopen. Restored state is revalidated by BrowserSession before use.
Favorite writes use one transactional URL-key mutation: two concurrent profile
handles preserve unrelated bookmarks, and a failed write restores the prior
in-memory favorite state and callback revision. The secondary-window registry
owns only a bookmark handle, so its shutdown cannot overwrite HSTS concurrently
saved by the primary browser.

Requirement trace: REQ-WEB-BROWSER-009, REQ-WEB-BROWSER-011.

Source:
`test/02_integration/os/hosted/browser_profile_store_spec.spl`

Updated: 2026-07-27.
