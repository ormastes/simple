# Browser Profile Store Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 1 | 1 | 0 | 0 |

The hosted browser profile owner writes versioned SQLite bookmark and HSTS
state, closes it, reopens the same profile, rejects corrupt file-scheme,
public-suffix records, and proves removal remains durable after another
reopen. Restored state is revalidated by BrowserSession before use.

Requirement trace: REQ-WEB-BROWSER-009, REQ-WEB-BROWSER-011.

Source:
`test/02_integration/os/hosted/browser_profile_store_spec.spl`

Updated: 2026-07-27.
