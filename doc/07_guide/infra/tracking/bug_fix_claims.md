# Bug Fix Claims (LLM wiki: bug tracking / debug workflow)

Concurrent agents must not fix the same bug. A bug being fixed is marked
`status=fixing` in `doc/08_tracking/bug/bug_db.sdn` and has a row in the
`bug_fix_claims` side table. Helper: `sh scripts/check/bug-claim.shs`.

## Rules for every agent

1. Run `sh scripts/check/bug-claim.shs reap` before triaging (reverts abandoned
   `fixing` bugs; `reap --report` only lists them).
2. Request bug details with intent:
   - `show <bug_id> --intent not_for_fixing` is read-only (triage, reading).
   - `show <bug_id> --intent for_fixing --session <id>` prints the same details
     and atomically claims the bug. Exit code 3 means another live session holds
     it (holder, since, last heartbeat are printed): pick another bug.
   - `--intent` is required; omitting it is a usage error (exit 2).
3. Never fix a bug that is `fixing` under another session.
4. While working call `heartbeat <bug_id> <session>` at least every 2 h. A claim
   with no heartbeat for more than 24 h is STALE and may be taken over or reaped.
5. When finished: `done <bug_id> <session> [--pr <n> | <n>]` (PR optional) once the PR is merged (status
   becomes `fixed`, note records the PR), or `release <bug_id> <session>` if you
   stop (status returns to the previous value).
   If implementation exists but a required verification remains, use
   `wait-verify <bug_id> <session> "<concrete required check>"` instead. This
   records the owner and waiting timestamp, releases exclusive fixing ownership,
   and sets `fix-implemented-verification-pending`. A verifier claims it again
   before running or repairing the remaining check.
6. Session id: first 8 chars of the Claude session id or agent id plus a lane,
   for example `a6dffc9c/p0f-1`.

Closed bugs (`closed`, `fixed`, `invalid`, `resolved-*`, ...) need no claim and
cannot be claimed (exit 4).

## Data

Main tables keep exactly 10 columns (bug-gen requires it); a claim only changes
`status` (to `fixing`) and `updated_at` there. Side table:

```
bug_fix_claims |bug_id, state, session_id, claimed_at, heartbeat_at, prev_status, note|
```

Full schema, exit codes and caveats: `doc/08_tracking/bug/README.md`.

## Status and ownership table

| Main status | Meaning | Linked details |
|---|---|---|
| `open` | Available for investigation; no fix acceptance claimed | Historical claims remain available |
| `fixing` | An agent is actively implementing or verifying | Current `bug_fix_claims` row: `session_id` identifies who, `claimed_at` records start, `heartbeat_at` records liveness |
| `fix-implemented-verification-pending` | Implementation exists; required verification is waiting | `waiting_verify` event records submitting `session_id`, transition time in `claimed_at`, and the required check in `note`; preceding fixing event preserves original work start |
| `fixed` | Reviewed fix landed through a merged PR | `done` event records session, completion time and PR number |

Run `status <bug_id>` to see both main status and owner details. Run
`check <bug_id>` for a read-only owner/start/check consistency check (exit 1 on
missing required links). Historical pending rows without a `waiting_verify`
event are reported for reconciliation; this command never invents an owner.
`waiting_verify` is not an active fixing claim, is not reaped, and does not
require heartbeats. Releasing a verifier's later claim restores the pending
main status; the historical waiting event still contains its required check.

Writers serialize through a directory lock containing the shell owner's PID.
Lock contention fails after bounded retries; age never overrides an owner.
Recovery requires stopping all writers, verifying the owner is gone, and
removing the abandoned lock manually. Cleanup removes only the caller's own
lock. Automatic stale-lock renames are unsafe because another writer can
replace the directory between inspection and removal.

## Where found and reproduction environments

`reproducible_by` in the original bug row names a reproducer/test/actor;
`bug_scope` classifies scope. Neither proves where a bug was observed.
Record environment evidence separately:

```
bug_environments |bug_id, found_env, reproduction_env, reproduction_state, evidence, recorded_at|
```

Use `environment <bug_id> <found-env> <repro-env> <unknown|candidate|verified> <evidence>`.
Labels can describe OS, architecture, runtime/producer and relevant build.
`found_env` is an observed environment and requires an evidence reference unless
it is `unknown`. A possible reproduction environment is `candidate`, explicitly
unverified. Only retained execution evidence permits `verified`. Missing data
stays `unknown`; provisional common scope never implies Windows compatibility.
The append-only table keeps observations by bug ID, and `show` displays them.
