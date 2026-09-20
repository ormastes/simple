# Slang backend closes library without honoring native teardown
## Closed 2026-09-16 — ...teardown Date: 2026-09-08. Status: fixed on the S3 independent-request implementation lane

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

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

