# Windows managed stream native ownership capsule

The implementation keeps legacy PTY operations and managed RAW launch/poll/IO/
cleanup in `src/lib/nogc_sync_mut/io/windows_pty_owner.spl`. That file exceeds
the normal 800-line guideline under the explicitly approved ownership exception.
Splitting the native operations through exported raw-state load/store ports let
outside callers overwrite authoritative HANDLE snapshots. Package visibility
currently has warning diagnostics and is not claimed as a hard security boundary.

The cohesive owner has private state, pin/hash helpers and revision-checked commit
ports. The public native/policy/launch siblings forward only typed public
operations. A successful commit increments the authoritative revision; stale
snapshots and any overwrite of a closed slot are rejected. Confirmed terminal
proof survives partial native cleanup so a released process HANDLE does not
prevent retrying a remaining Job, CNG provider, file pin or heap release.

Every legacy and managed PTY entry is bound to one actual owning thread. A
narrow native platform helper atomically publishes a retained real thread HANDLE
under a short SRW lock. Each entry checks the HANDLE is still nonsignaled and
its actual ID matches the current thread. An exited or failed owner is never
rebound implicitly, including when Windows recycles a DWORD thread ID. The
binding HANDLE belongs to the process-lifetime native capsule, not a helper
Job's cleanup receipt. Initial failed HANDLE release remains retained there.
No guard lock spans hashing, launch, IO polling or cleanup in the caller.

The first actual groups/processor-count/quantum observation establishes the
service's native CPU profile. Managed leases retain it. A changed or unavailable
profile during poll closes input/admission, requests exact Job cancellation,
and keeps ownership charged until actual leader exit, Job emptiness and pending
IO completion. New admissions remain blocked after drift until deployment
requalification; the owner never silently rewrites affinity or CPU rates.

Deployment qualification must guarantee stable processor topology for the
helper lifetime. Dynamic CPU hotplug/group changes are unsupported. Polling
cannot prove an instantaneous absolute CPU cap across a topology change.

Status: source-only **NOT_RUN**. Compiler import-privacy enforcement, actual
Windows Job behavior, failure injection and full cleanup remain qualification
gates; this document does not turn source assertions into execution evidence.
