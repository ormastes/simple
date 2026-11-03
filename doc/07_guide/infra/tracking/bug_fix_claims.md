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
