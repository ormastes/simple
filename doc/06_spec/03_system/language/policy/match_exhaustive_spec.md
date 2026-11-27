# Non-exhaustive value match is diagnosed

**Spec:** `test/03_system/language/policy/match_exhaustive_spec.spl` (+ `match_exhaustive_staged_spec.spl`, tagged in-development)
**Requirement:** match exhaustiveness: warning now, error staged
**Group:** diag

| Scenario | Status | File |
|----------|--------|------|
| emits MEXH001 at warning severity for a missing enum variant | passing | match_exhaustive_spec.spl |
| names the missing variant | passing | match_exhaustive_spec.spl |
| is silent when every variant is covered | passing | match_exhaustive_spec.spl |
| is silent when a wildcard arm absorbs the rest | passing | match_exhaustive_spec.spl |
| keeps a missing variant a warning for non-critical profiles and an error for critical | passing | match_exhaustive_spec.spl |
| does not escalate a fully covered match even under critical | passing | match_exhaustive_spec.spl |
| makes the default-profile missing-variant diagnostic an error (severity 1) | in-development | match_exhaustive_staged_spec.spl |

Passing: 6; in-development: 1.
