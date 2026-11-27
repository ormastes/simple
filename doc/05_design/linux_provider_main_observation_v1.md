# Installed original-main observation and retained cutoff preparation

**AUTHORED_NOT_RUN.** This implements the finite read-only scope selected by
the architecture lead after reviewing provider-stop safety. It does not enable
a signal, provider mask, provider `StopUnit`, restart, full cutoff, request
drain, inventory release, helper closure, successor handoff or machine genesis.

REQ-LINUX-PROVIDER-MAIN-OBSERVATION-001 requires genuine installed provenance,
actual original-process pinning and an actual endpoint-peer correlation.
REQ-LINUX-PROVIDER-MAIN-OBSERVATION-002 retires active aliases in the original
canonical supervisor before native acquisition and retains original exclusion
through every unknown outcome. REQ-LINUX-PROVIDER-MAIN-OBSERVATION-003 requires
actual typed preflight observations and consumed/retained cleanup without
converting them into stop-transaction authority.

The accepted supervisor R2 remains immutable historical source under
`/tmp/linux-installed-supervisor-fence-20261115-r2`. This source revision adds
the continuation in the existing supervisor registry; no second global lock,
journal, writer or metadata-to-fence constructor is introduced. The original
machine authority/writer remains the upper composition's responsibility. This
read-only continuation neither extracts nor transfers that writer.

`begin_provider_cutoff_v1()` returns only `Rejected(original, reason)` before
arming or `Retained(opaque same-registry cutoff owner, typed phase, reason)`.
It first validates the actual active owner, then records
`provider-cutoff-retained` before native acquisition. Both existing active
APIs reject that phase, including aliases copied before arming. Repeating the
active continuation cannot reissue work. There is no Ready variant.

The normal retained reason is exactly
`provider-stop-transaction-ownership-unavailable`. A process-only `KillMode`
and empty stop commands cannot own systemd's reverse/forward dependency
transaction, `OnSuccess`/`OnFailure`, emergency actions, IPC removal, dynamic
user cleanup, runtime directory cleanup, or other automatic teardown. A
unit-load timestamp and `NeedDaemonReload=false` are not a retained manager
configuration generation or transaction lock. This source does not extend a
property whitelist indefinitely or silently promote it to that missing
producer. A separately bounded manager transaction/confinement design is
required before any provider stop branch can be enabled.

The new main-observation helper accepts actual opaque installed-profile and
authenticated-bus owners. There are no caller PID, endpoint, root, unit-list,
bytes or raw-FD constructors. The monotonic deadline is only a bounded request
input: it must lie within the next 30 seconds and cannot establish authority.
It reads the provider from the genuine root profile, correlates exact unit
`Id`, active state, `MainPID`, and manager-owned process membership, and opens a
real original pidfd before looking up the target through genuine procfs.

Every native output enters private canonical cleanup state before validation.
Fresh procfs must be genuine and its `self`/`thread-self` links must agree with
the actual current installed process. The target's directory device/inode/
mount identity, native start ticks and all four UID values are read through
retained descriptors. A pidfd already reporting exit is refused during initial
capture; the same original process must remain live through final correlation.
Pin-before-lookup plus final readiness/incarnation checks prevent PID reuse
from substituting another process during acquisition.

The helper decodes the root profile's installed-v3 provider policy using the
existing pure data decoder, with an explicitly qualified async-family import.
All native IO/lifetime ownership remains synchronous; no global configured
library selection is changed. The helper acquires and retains one actual
`LocalUnixConnectionV1`, verifies its native peer UID and PID against the
installed dedicated account and original provider, and retains its socket
device/inode. It sends no HTTP request. This is peer correlation only: one
client connection does not own the server listener, accepted streams, old
requests or ingress closure. Socket-activated topologies whose connect-time
peer differs from the original main process refuse this supported capture.

Actual read-only preflight uses fixed-arity sd-bus variant readers for booleans,
the signed-positive subset of unsigned64 values, bounded string arrays and
exact `ExecStop`/`ExecStopPost` command-array types. It records `KillMode`,
`Restart`, `ControlPID`, actual command-list emptiness, `DynamicUser`,
`RemoveIPC`, `RuntimeDirectory` and `TimeoutStopUSec`. Malformed/missing fields
refuse; recorded values are observations rather than a complete stop-plan
certificate. No field authorizes effects, even if all values look restrictive.

Preflight fields are captured once during initial acquisition. `current_v1()`
refreshes process identity while live, the installed profile, manager identity
and original-process exit observations; it returns the retained initial
preflight fields. `observed_monotonic_nanos` dates those current lifetime
checks, not a fresh preflight sampling or configuration generation.

The original supervisor compares the captured PID/incarnation with its own
already-retained original identity. A disagreement retains unknown ownership.
Later `poll` on that exact pidfd can observe original-process exit. `POLLIN` or
`POLLHUP` is exit evidence for that kernel object; invalid/error/unexpected
events are not absence. The observer never calls `wait` and never describes a
nonchild exit as a reap. A natural exit yields
`MainExitedClosureUnknown`, retaining the precise missing-transaction reason
and all helper/request/store obligations. It does not certify all old actors
or interrupted operations.

All registry/native public entries first invoke the accepted permanent
`linux_machine_process_origin_check_v1()` guard. The pure proc codec extracted
from the existing supervisor contains only decimal/UID/start-time decoding;
its data cannot construct an owner. Existing supervisor decoding behavior is
preserved behind imports of that codec.

Native acquisition has one finite 30-second cutoff acceptance deadline,
including validation before arming. String arrays are bounded to 128 entries/
65536 bytes; each string to 4095 bytes; proc entries to 65536 bytes; each helper
to 16 native proc descriptors and one pidfd/client connection; the registry to
256 owners. No polling sleep or retry campaign is added. Later lifetime
observations may read the pinned process without creating another owner or
extending any effect deadline. There are no permitted provider effects.

Cleanup closes only owned client/proc/pidfd resources. It never closes the
borrowed installed profile or manager bus and never unlinks a socket. Positive
native consumption is recorded before close; errors preserve the first
diagnostic. An unconfirmed client close keeps its exact owner quarantined and
does not retry a possibly consumed handle. Repeated positively consumed close
returns the recorded result. The outer cutoff retains original global
inhibition after observation cleanup; no old active alias is revived.

Actual native qualification remains unavailable. The unique actual-fixture
spec/manual exercises same-registry alias retirement, live original identity,
typed observations and observation-only cleanup, but is **NOT_RUN**. Natural
exit, cleanup faults, namespace/peer substitution and all effect/handoff paths
remain **NOT_COVERED**. Linux pidfd support and the actual libc `pidfd_open`/
`poll` and libsystemd ABI must be admitted; no new Simple runtime export,
allowlist, seed execution, C shim or service installation is introduced.

Primary contracts: [pidfd lifetime and polling](https://www.kernel.org/pub/linux/docs/man-pages/book/man-pages-6.17.pdf),
[systemd process killing modes](https://www.freedesktop.org/software/systemd/man/latest/systemd.kill.html),
[actual manager properties and commands](https://freedesktop.org/software/systemd/man/latest/org.freedesktop.systemd1.html),
and [automatic IPC teardown](https://www.freedesktop.org/software/systemd/man/259/systemd.exec.html).
