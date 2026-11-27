# Darwin direct-child broker admission

The launchd observation primitive remains unchanged: a same-UID actor can replace
a label before its first observation, and GetJob does not expose the replacement
environment. No launchd label, discovery result, or claimed PID grants admission.

`runtime_sosix_darwin_broker_admission_private.h` provides a separate direct-child
bootstrap for the canonical `sosix_darwin_broker_helper.c`. It admits that helper
with kernel spawn authority and an empty environment established before dyld,
rather than trying to attest launchd job provenance retrospectively.

## Trust and lifecycle

The controller owns a `SosixDarwinImage` created through `create_bound` from a
trusted SHA256 digest of the canonical helper. Existing image provisioning binds
its bytes to an AMFI CDHash, strips entitlements, enables hardened runtime, rejects
embedded dyld environment commands, and constrains non-system libraries. Keep the
image live through spawn. A cooperative image is rejected with `ENOTSUP`.

`spawn_closed` passes a literal empty environment, closes nonstandard descriptors
with `POSIX_SPAWN_CLOEXEC_DEFAULT`, opens standard streams on `/dev/null`, changes
cwd to `/`, and resets signal mask/dispositions. This prevents inherited variables
or descriptors from reaching dyld, library initializers, and helper constructors;
clearing environment in helper main alone would be too late.

The returned direct-child PID remains owned and unreaped. Its kernel unique ID
and PID version are recorded. The controller is the sole reaper: no SIGCHLD
handler or other thread may collect this PID. PID retention, not a launchd label,
prevents pre-observation replacement. Calls on an owner must be serialized.
Even if the identity query fails because the helper exits immediately,
`spawn_closed` retains child ownership; callers must close/reap after every
successful spawn, whether admission succeeds or fails.

The helper connects to a caller-owned listener and checks `LOCAL_PEERTOKEN`
against the controller PID/version before sending readiness. The controller
checks the accepted stream token against its direct child's identity and verifies
CDHash via `csops_audittoken` before sending `A`. The canonical helper replies
`A`, accepts only `P` ping and `Q` shutdown, and never executes a workload, forks,
passes sockets, or execs. The caller owns and closes the accepted descriptor.
A connection timeout or failed handshake must be followed by owner cleanup.

The helper's connect and read operations have finite monotonic deadlines.
Admission uses one shared timeout for readiness and acknowledgment. The close
operation signals and reaps only the retained direct child, including a stopped
child. `ECHILD` fails without signalling: it is lost authority, not successful
cleanup. The bounded close can return a timeout; ownership remains live for a
later cleanup attempt. An owner cannot be reused after reaping.

## Scope boundary

A direct child normally shares the controller's coalition. This bootstrap does
**not** supply disjoint-coalition authority, workload execution, descendant
confinement, resource budgets, descendant reaping, or a BuildRunner V4 provider.
The existing launchd broker and production provider remain observation-only and
fail closed respectively. A kernel-owned isolated job boundary is still needed
before combining this admission primitive with a complete workload owner.

Same-UID denial of service (signals, endpoint unlinking, backlog flooding) may
prevent startup; it must not authorize a substituted helper. Compromise of the
trusted controller, its digest inputs, or its sole-reaper contract is outside
this primitive's trust model.
