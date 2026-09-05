# sspec: hollow-expect provisional text clobbers real failure message (2026-08-19)

**Status:** OPEN (filed only; fix deliberately deferred)
**Site:** `src/compiler_rust/compiler/src/interpreter_call/bdd.rs:1134`

## Mechanism

When a matcher PASSES, the code clears the BDD failure *flag* but does not clear
`BDD_FAILURE_MSG`. The hollow-expect detector writes a provisional message
("hollow expect" text) before matcher evaluation; on the pass path that
provisional text is left standing in `BDD_FAILURE_MSG`. When a *later* expect in
the same test genuinely fails, the reporter can surface the stale provisional
hollow-expect text instead of (or clobbering) the real failure's message, so the
diagnostic shown for the failing expectation is wrong/misleading.

## Fix sketch

On the matcher-pass path at bdd.rs:1134, clear `BDD_FAILURE_MSG` alongside the
failure flag (or scope the provisional hollow-expect message so it is consumed
or discarded per-expect rather than per-test).

## Found while

Debugging closure_captured_instance_loses_method_self_mutation_2026-08-19 — the
secondary defect made the primary failure's message unreadable.
