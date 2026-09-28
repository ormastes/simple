# Spawn child capability commit V1

The focused scenario verifies that an already-attenuated pledged capability
pouch is rebound to the scheduler-reserved child identity before either the
generic staged task or authenticated loader task becomes visible. Token kind,
generation, ancestry, and delegation depth remain unchanged.

Authenticated adoption reserves a paired task/lifecycle identity, constructs
the child TaskId from that exact pair, and stores the pair's lifecycle
generation alongside the rebound CSpace before TCB publication. The legacy
ID-only allocator is not accepted by this source contract.

Evidence class: source-contract and capability-value scenarios. SSpec execution
and generated documentation remain **MissingEvidence** without an admitted
self-hosted runner; this authored manual does not attest guest execution.

It also records the current fail-closed boundary: scalar VMM copy is necessary
but does not authorize syscall 13. Scheduler-owned caller acquisition, retained
authenticated VFS binding, stdio inheritance, and asynchronous wait/reap still
require physical integration evidence.
