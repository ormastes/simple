# Linux leaf adapter for Simple Container API V2

Status: **AWAITING_VERIFICATION** source work. No native execution, runtime tests,
SPipe/docgen, compiler/lib/MCP checks, or performance qualification are claimed.
The adapter composes the existing Linux OCI provider and canonical common API;
it does not add another scheduler, fake provider, or signature verifier.

## Native observation and scope

`observe(policy_bytes)` decodes canonical protected operator policy, obtains one
actual engine-policy observation, and reads bounded no-follow native machine and
boot identifiers from `/etc/machine-id` and `/proc/sys/kernel/random/boot_id`.
Runtime OS comes from the canonical native platform owner. Kernel architecture
comes from the new bounded Linux `uname` owner, never environment variables,
shell output, a compile-target guess, or an x86 default. Unknown native evidence
fails closed.

`open` validates the common scope and trusted state directory, constructs the
existing managed Linux provider once, and reuses its actual retained engine
observation rather than probing it twice. Actual machine ID is compared with
`scope.native_machine_id`; `physical_host_id` remains a logical host alias.
Linux finite opens accept only `native-boot-incarnation-v1`, with actual native
boot equal to `scope.boot_id` and `scope.continuity_id`. Weak counters and
service-incarnation authority require another admitted persistent owner and are
explicitly unsupported here. `observation()` returns the cached actual open
snapshot; it makes no claim that a new engine probe was performed.

The provider's `node_boot_id` and retained intent field use
`container_scope_fence_id_v2(scope)`, the opaque common compatibility fence over
the complete scope. This is intentionally distinct from actual native boot,
which remains separately observed and compared. Legacy direct V1 constructors
are unchanged.

## Request and effect boundary

The adapter decodes the existing canonical retained Linux request, recomputes its
digest, and checks backend, workload UID, attempt, operation ID, and all seven
scope fields. Projection reports actual CPU, memory, timeout, device absence
(the current codec has no accepted device field), and any bundle/build workspace
intent. Projection does not authorize devices or workspace access; leaf
capability validation and caller authority remain required.

The common API dispatches the actual opened adapter for prepare/create/start,
read-only inspect/logs/wait, authorized stop/destroy, intent, and recovery.
Unknown actions reject before native effects and returned turns retain the real
owner. Existing leaf receipt details are preserved, including `prepare_pod` for
the common prepare action. Generic destroy uses `force=false`; callers must
authorize and perform stop first when necessary.

Managed create accepts one full 64-hex native ID, optionally followed by a single
LF or CRLF. Names, partial IDs, option-like values, multiple IDs, or extra stdout
remain uncertain effects. Reconciliation requires the retained V2 request and
all original identity fields; verified full native identity is published through
the existing journal writer before a qualified recovery result is returned.
Publication failure retains uncertainty. V1 records are never promoted by this
path, and conflicting saved native IDs cannot be overwritten.

Trusted consumers install `ContainerEffectDeadlineV1` only for new create/start
launches after verifying their grants and approvals. The leaf rechecks native
clock expiry immediately before execution. Read/recovery and retained authorized
cleanup do not borrow an expired launch grant. Grant expiry never kills an
already running workload. The separate operation duration is capped at
`min(open_timeout_ms, request.timeout_ms)`; expiry is not converted to a process
lifetime timeout. Adapter calls sharing a provider must be serialized.

Intent lookup reuses the leaf's strict retained binding reader. Recovery compares
the complete actual retained intent, including phase, before invoking existing
native reconciliation. Caller-supplied metadata cannot replace durable identity.
Legacy V1 exact-ID cleanup remains governed by the leaf's explicit migration
rules and cannot authorize new execution.

## Native architecture owner

`src/lib/nogc_sync_mut/sffi/linux_uname_v1.spl` is a Linux-only libc boundary.
The local `/usr/include/linux/utsname.h` and
[Linux UAPI definition](https://github.com/torvalds/linux/blob/master/include/uapi/linux/utsname.h)
define six 65-byte fields; the owner allocates 390 bytes and reads only bounded
sysname and machine fields at offsets 0 and 260. The
[uname manual](https://man7.org/linux/man-pages/man2/uname.2.html) documents the
native call and return status.

The owner reuses canonical malloc/free and volatile byte helpers, frees the
allocation on every return path, requires NUL termination and ASCII supported
architecture identifiers, and rejects other layouts/platforms. Compile-time
64-bit ABI gates protect pointer/size_t calls only; architecture returned to the
API is always decoded from the actual native result. This source boundary has
not been executed or certified for any producer/platform.

## Evidence and remaining limits

Focused tests wrap a real scripted Linux leaf in the common API's explicitly
named test-only owner factory. They exercise canonical projection, mismatched
scope and payload refusal, lifecycle dispatch, launch expiry, retained recovery,
and fixture-scope safety. Pure uname decoder tests and a direct native probe are
authored separately. Synthetic fixture observations are never production
configuration or native enrollment evidence.

The common facade defensively validates/projects before effect dispatch; each
stage currently rechecks bounded canonical request data. No warm-startup,
latency, RSS, native FFI, or full container conformance result is claimed. The
known producer/toolchain constraints and the combined source dependency set
must be resolved before executing the required checks.
On 2026-11-07 the local `command -v podman` check returned no executable
(status 1). No backend installation, service startup, image pull, or live
container test was performed.

## Fresh wait and independent absence

Common wait explicitly requests a fresh exact-native observation even after an
exited/stopped cache. The raw stdout/stderr and native CLI status remain distinct
from the parsed workload exit code. Destroyed state without a retained qualified
wait receipt returns `wait-retained-evidence-unavailable`; it does not invent an
observation or query a removed object. The host must retain original wait proof
before destruction; durable replay of missing raw proof remains an explicit gap.

Absence invokes the leaf's separate exact full-ID `container exists` query.
Only its documented absent result with clean output produces a receipt. Query
and complete operation hashes come from the actual routed command/observation,
using the common canonical evidence helpers. Receipts include the full scope,
request digest, provider identity and native observation time. They are integrity
data, not producer authentication. The adapter does not mutate lifecycle
journals or release host capacity. Destroyed tombstones without a query are not
absence evidence.

Current authored evidence: 15 common-API scenarios and 2 pure uname scenarios,
with matching authored manuals and one unexecuted native uname entrypoint. All
17 cases remain UNEXECUTED; no test runner, build, native syscall probe, or
container process was invoked by this worker.
