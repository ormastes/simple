# Query/LSP W0404 configuration false green
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Symptom

`@allow(visibility_boundary)` and `@deny(visibility_boundary)` did not affect
the Query/LSP wide-public diagnostic W0404, although the public lint CLI did.

## Root cause and fix

`query_lint._governed_lint_codes()` omitted W0404, so it never received the
shared severity override. Add W0404 to that shared list and cover allow/deny
through the existing query/LSP severity oracle.

