# Live release-policy drift verifier is missing

**Status:** Open release blocker
**Owner:** VCS policy and GitHub administration maintainers

## Evidence

`.spipe/policy/vcs.sdn` declares protected refs, immutable candidate/tag rules,
and live verification requirements, but `src/app/sj/lifecycle_policy.spl` does
not yet enforce the complete `rebase`, `release`, and `live` sections against
GitHub server state. Local policy therefore cannot prove that the remote accepts
only the intended mutations.

## Unblock condition

Implement normalized expected-ruleset rendering plus read-only live diff and
verify commands. Candidate creation and promotion must fail closed when the
remote fingerprint differs. Add fixtures for absent protection, bypass actors,
tag update/delete permission, stale policy hashes, and unavailable GitHub state.
