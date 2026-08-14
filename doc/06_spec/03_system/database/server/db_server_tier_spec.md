# DB server tier: session isolation and capability denial

Source: `test/03_system/database/server/db_server_tier_spec.spl`

## Primary operator flow

1. **Authenticate the database principal.** Missing, wrong, and unknown
   credentials fail with the same authorization category. Successful login
   returns a capability-bound session.
2. **Exercise connection cleanup.** EOF drains the bounded transport, closes
   sessions opened by that connection, and discards abandoned overlays.
3. **Prevent observation of the P3/P4 window.** Peer reads cannot see staged
   writes, while an unconditional committed control is visible. An injected
   store leak is designed to show the isolation oracle changes outcome when the
   invariant is violated; execution remains uncredited.
4. **Apply the denial matrix.** Read-only, empty, wrong-table, missing-table,
   and write-only grants cannot widen into ungranted access.
5. **Bound batch and range work.** Oversized input fails before mutation and
   range results have deterministic order and an explicit limit.

## Evidence boundary

The source has non-vacuous absolute assertions. It has not been executed or
regenerated in this lane: no runtime PASS, coverage percentage, docgen receipt,
or deliberate-red transcript is claimed while Stage 4 is unhealthy.

No executable `.spl` is stored below `doc/06_spec`; this manual contains no
stub scenario.
