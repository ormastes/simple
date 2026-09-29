# Release workflow still rebuilds after a tag
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** Closed in release-process hardening branch; live beta evidence pending
**Owner:** Release CI maintainers

## Evidence

`.github/workflows/candidate.yml` now builds and qualifies an immutable,
durably reserved candidate attempt. `.github/workflows/release.yml` consumes
that exact artifact ID/name/digest and contains no bootstrap/build path.

## Unblock condition

Satisfied by the split candidate/promotion workflows and focused adversarial
source contracts. Closure is implementation evidence only; an actual beta
promotion remains required for release PASS.

