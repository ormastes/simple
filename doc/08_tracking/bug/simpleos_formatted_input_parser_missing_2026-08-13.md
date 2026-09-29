# SimpleOS formatted-input parser is unavailable
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Guest libc now fails closed and supplies every declared formatted-input symbol.

## Fault and repair

`vsscanf` previously returned zero without parsing, while `scanf`, `fscanf`,
and `sscanf` were declared but had no guest providers.  The shim now returns
`EOF` and sets `ENOSYS` consistently for all four APIs.

## Unblock condition

Implement a bounded parser with exact conversion/assignment rules, overflow
handling, width limits, and a complete test matrix before promoting any of
these APIs.  Parsing untrusted configuration must not use this stub surface.

