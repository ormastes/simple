# DB server tier: session isolation and capability denial

Source: `test/03_system/database/server/db_server_tier_spec.spl`

Status: **manually source-synchronized 2026-08-16; current Stage-4 execution,
maintenance scorecard, and docgen receipt remain pending.**

## Primary operator flow

1. **Authenticate the database principal.** Missing, wrong, and unknown
   credentials fail with the same authorization category. Successful login
   returns a capability-bound session.
2. **Bind the production listener.** Bind an ephemeral loopback address,
   prequeue a real client, exchange an authenticated `OPEN`, and verify exact
   framed output over the owned TCP transport.
3. **Shut down and release the connection.** EOF drains the bounded transport,
   closes sessions opened by that connection, and releases the address for
   rebind. The parent retains only `DbStopControl`, observes its shared
   accept-attempt receipt, then requests stop. The serving owner returns from
   the bounded accept, rejects any connection completed after stop before
   authentication or session dispatch, and closes the mutex-owned listener
   state. No raw fd crosses to the stopping domain; copied controls see the
   shared closed state.
4. **Prevent observation of the P3/P4 window.** Peer reads cannot see staged
   writes, while an unconditional committed control is visible. An injected
   store leak is designed to show the isolation oracle changes outcome when the
   invariant is violated; execution remains uncredited.
5. **Apply the denial matrix.** Read-only, empty, wrong-table, missing-table,
   and write-only grants cannot widen into ungranted access.
6. **Bound batch and range work.** Oversized input fails before mutation,
   range results have deterministic order and an explicit limit, and quoted or
   unquoted multibyte UTF-8 values survive request parsing and batch reads.

## Evidence boundary

The source has non-vacuous absolute assertions, including retained-copy idle
shutdown, post-stop connection rejection with zero accepted/active/session
state, and the adjacent quoted UTF-8 parser oracle. It has not been executed or
regenerated in this lane: no runtime PASS, coverage percentage, docgen receipt,
or deliberate-red transcript is claimed while Stage 4 is unhealthy.

No executable `.spl` is stored below `doc/06_spec`; this manual contains no
stub scenario.
