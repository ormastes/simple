# Browser HSTS persistence owner is missing
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Implementation fixed; executable cross-process evidence remains blocked by the
recorded production target compiler/link failure.

## Evidence

BrowserSession enforces bounded in-session `max-age` and `includeSubDomains`
policies. `BrowserProfileStore` now persists validated wall-clock receipt and
expiry state in the hosted browser profile, and the production registry
converts it back to the session monotonic clock only for browser app windows.
No maintained preload list is claimed.

## Implemented fix

The versioned SQLite owner retains at most 1024 unique hosts and rejects IPs,
public suffixes, corrupt booleans, expired policies, and lifetimes above ten
years. Browser-window close persists before destruction.

Do not serialize the session-monotonic expiry directly. The profile broker must
own wall-clock receipt/expiry and convert only validated remaining lifetime at
the BrowserSession boundary.

## Required evidence

The file-backed integration scenario proves reopen persistence, subdomain
upgrade, corrupt-row rejection, expiry/removal, and durable removal. Existing
BrowserSession security evidence proves HTTPS-only acquisition. A real
target-process restart remains required before claiming runtime PASS.

