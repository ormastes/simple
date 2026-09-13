# Query/LSP W0404 configuration false green
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

`@allow(visibility_boundary)` and `@deny(visibility_boundary)` did not affect
the Query/LSP wide-public diagnostic W0404, although the public lint CLI did.

## Root cause and fix

`query_lint._governed_lint_codes()` omitted W0404, so it never received the
shared severity override. Add W0404 to that shared list and cover allow/deny
through the existing query/LSP severity oracle.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
