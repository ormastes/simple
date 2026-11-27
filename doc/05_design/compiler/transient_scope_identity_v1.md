# Actual transient scope identity

`transient_array_scope_identity_v1()` observes the selected runtime's actual
current transient scope. Zero means no scope belonging to the calling owner.
A positive identity remains stable while running or paused. Refused nested
begin does not replace it. End retires it; a later successful begin gets a fresh
identity even when both observations report running state 1. The current owner
has no resume or nested-scope operation, so no such behavior is invented here.

The native C provider reuses its existing TLS scope ID and process-wide atomic
nonwrapping allocation counter. A foreign thread observes zero and cannot
pause, end, or replace the live owner's scope. The pure-Simple provider reuses
its existing scope ID and nonwrapping counter under its explicitly single-thread
contract. It does not advertise TLS or foreign-thread safety. The bootstrap
reference stores a nonwrapping process-unique ID on each real TLS scope; unlike
native C, independent reference threads can own independent simultaneous scopes.
Exhaustion permanently refuses new scopes rather than reissuing an identity.

The observation grants neither a borrowed lease nor permission to reclaim,
pause, resume, promote, or mutate a caller's owner. Missing runtime support must
remain a link/extern error; an absent provider is never backfilled with zero.
This identity is separate from AST handle incarnation, schema context identity,
and array value/COW capability. It admits no builder or retained topology cache.

The focused native test includes the entire canonical native provider, without
allocator replacements. It checks inactive, running, pause, refused nested begin,
foreign-thread isolation, end/reentry and the actual terminal counter IDs. The
private counter is advanced only inside that isolated test process to exercise
exhaustion in bounded time. The Simple integration probe and bootstrap-reference
tests are authored separately; execution receipts must distinguish these paths.
