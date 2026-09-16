# Temporary Rust recovery runner remains alive after passing examples

**Status:** REPRODUCED / PURE-SIMPLE QUALIFICATION PENDING
**Severity:** P1 — a green focused run does not terminate

## Reproduction

The explicitly opted-in `SIMPLE_TEST_RUNNER_RUST=1` recovery run executed the
three structured-evidence examples successfully, printed `3 examples, 0
failures`, then remained alive for an unknown owner until the enclosing
60-second timeout returned
124. It also emitted more than 160,000 diagnostic lines before the examples.
No matching child remained after the timeout killed the process group.

## Required solution

Keep recovery output redirected and bounded. Trace the Rust recovery runner's
post-result owner and diagnostic source before using it again; a printed green
summary is not completion evidence. Production qualification remains the
bounded pure-Simple Stage4 essential-tools smoke, which must exit normally.

## Evidence

- structured-evidence examples: 3 passed, 0 failed
- enclosing recovery command: exit 124 after 60 seconds
- post-timeout matching child scan: empty
