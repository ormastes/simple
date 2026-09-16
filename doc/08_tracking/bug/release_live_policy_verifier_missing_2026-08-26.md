# Live release-policy drift verifier is missing
## Obsolete 2026-09-16 — referenced path(s) gone, e.g. scripts/release/github-policy.shs verify-live

Reviewed in the 2026-09-16 bug-ledger normalization pass. Kept for history;
the subject is removed, superseded, or duplicated elsewhere in the ledger.

**Status:** Closed in release-process hardening branch; monitored for live drift
**Owner:** VCS policy and GitHub administration maintainers

## Evidence

The typed policy now projects seven GitHub rulesets plus protected integration,
release, and npm environments. `scripts/release/github-policy.shs verify-live`
normalizes and compares live provider state and immutable-release settings.

## Unblock condition

Satisfied by the policy projection/live verifier and provider contract tests.
Candidate creation and promotion remain fail-closed on policy drift.

