# Slang backend closes library without honoring native teardown

Date: 2026-09-08. Status: open S3 correctness blocker.

`model_executor/backend.spl::close_backend` invokes the native free function but
does not inspect its result before calling `spl_dlclose`. S1/S2 native teardown
currently always succeeds, but independent requests require a busy refusal while
any request owns a context or prefix lease.

S3 implementation must return a typed busy/teardown error, retain the dynamic
library handle on failure, and prove with a fixture that unloading cannot race
or invalidate a live request. This must be fixed before independent-context
capability is advertised.
