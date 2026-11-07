# Effective allocation owner observation

Status: implemented and source reviewed. The full-native actual-owner fixture
built successfully and executed once with exit 0. Reference, Simple and W2
consumer execution remain UNEXECUTED and unqualified.

The current transient scope is not necessarily the owner of a new allocation.
While a module scope runs, `rt_session_alloc_begin/end` can redirect allocation
to the live session. Pausing also changes allocation selection without changing
the transient scope's identity. Scope state and scope identity alone cannot
prove that a pending cell and a newly allocated payload have the same lifetime.

The boundary observes the allocator's existing selection decision.
Native selection shares the exact predicate already used by
`rt_core_transient_scope_for_new_object`; the reference inspects its actual
session allocation depth and live TLS scope. It does not reconstruct the owner
from scope state alone or create a separate authority counter.

The scalar ABI is `rt_allocation_owner_identity_v1() -> i64`: zero identifies
process allocation, a positive u32 identifies transient allocation, and a
negative u32 identifies session allocation. Disjoint signs prevent numeric ID
collisions between the two owners. A semantic facade decodes this into an
explicit domain and incarnation. Invalid encoding fails; missing support is
an unresolved extern, never a process-owner fallback. This grants no lease and
does not admit array value semantics or retained proof caches.

Pure-Simple currently owns its documented single-thread process/transient
allocator and has no session machinery in core_memory. Its implementation must
describe that actual capability; no fabricated session observer or mixed-owner
qualification is permitted. Full W2 session integration remains gated on the
selected provider composition proving the same allocation decision.

The native fixture surrounds actual allocations with session override begin/end,
running and paused module scopes, verifies actual owner registry assignment, and
exercises retirement/reentry. The separate Simple probe covers the common
process/transient observation without claiming session support. The consumer
must reject storing younger payloads
in older pending cells after override changes, before reading or writing the
cell. Prepared process roots must never retain scope-owned Option wrappers,
array capacity or dictionary capacity after leave. Native observer execution
and full consumer execution are separate evidence gates.
