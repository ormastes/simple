# Failed SDK readiness preserves an owned sentinel

Status: **AUTHORED_NOT_RUN**. Executable:
`test/03_system/tools/daemon_sdk_owned_sentinel_safety_v1_spec.spl`.
Requirements: DAE-02 partial, REQ-DAE02-SDK-SAFETY-001–003.

This actual native fixture requires an admitted Linux `OwnedProcessLease` V3
provider and the installed `/bin/sh` and `/bin/sleep`. It launches one child,
which prints its own PID and execs sleep under the same PID. Its actual lease
is retained; that PID is written only to a unique private fixture lock as
reproduction metadata. It is not converted into a process owner.

The fixture probes owned liveness before returning a failed ping. Unknown
liveness causes a successful callback result plus a recorded test failure,
preventing the unsafe old branch from signalling after that uncertainty. Only
the child created for this case can be the PID-file target; no test-process,
unrelated or pre-existing daemon PID is used. This fixture has not been executed.

| Scenario through sync and async exports | Expected production behavior |
| --- | --- |
| Existing live sentinel fails ping | False; no startup; one ping; same lock bytes; actual owned child still live |
| Startup publishes sentinel PID, then ping fails | False; one startup and ping; no replacement; actual child remains live |
| Startup publishes sentinel PID but returns false | False; one startup, no ping or signal; actual child remains live |

All six cases capture result, callback counts, lock bytes and actual owned
liveness before cleanup. Cleanup uses only `OwnedProcessLease` cancellation,
polling and collection; it never signals by the lock PID. Result assertions run
after that cleanup attempt. Failed cleanup retains the actual owner and private
root for diagnosis. No native/build campaign was run and no observed survival,
reaping or backend availability is claimed.

Collection publishes the actual mutated lease before examining terminal errors.
Positive consumption with an error keeps the diagnostic/root, not a stale
pre-collection handle; it cannot trigger another poll. Not-reaped/11/16 states
retain the updated live lease, and unknown collection is quarantined. A new
case refuses before replacing any retained root or lock metadata. These review
corrections do not add executed fault-injection evidence or reset the unknown
prior same-feature cycle count.

Full daemon protocol correctness, hostile PID reuse, exact-owner service restart,
crash recovery and other lock lifecycle operations remain outside this fix.
