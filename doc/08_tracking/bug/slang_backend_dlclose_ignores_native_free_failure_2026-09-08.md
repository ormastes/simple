# Slang backend closes library without honoring native teardown
**Status:** OPEN (unverified 2026-09-12)

Date: 2026-09-08. Status: fixed on the S3 independent-request implementation lane.

`model_executor/backend.spl::close_backend` invokes the native free function but
does not inspect its result before calling `spl_dlclose`. S1/S2 native teardown
currently always succeeds, but independent requests require a busy refusal while
any request owns a context or prefix lease.

S3 implementation must return a typed busy/teardown error, retain the dynamic
library handle on failure, and prove with a fixture that unloading cannot race
or invalidate a live request. This must be fixed before independent-context
capability is advertised.

Resolution: `close_backend` now checks native teardown before `spl_dlclose`,
and the engine retains its backend/model identity when teardown reports busy.
The native fixture holds independent requests open, proves unload refusal, then
closes them and proves teardown succeeds.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
