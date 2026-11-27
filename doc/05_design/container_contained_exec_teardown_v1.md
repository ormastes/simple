# Contained exec teardown evidence

Status: design and source inventory only. No containment capability, native
teardown receipt, runtime qualification or permission to release capacity is
introduced by this document. This is a new required capability, separate from
the closed `d41bf8b2ace96ace60a2620925a25b11cebbf153` exec-owner repair campaign.

## Decision

Keep lifecycle authority and observation separate. The existing signed parent
stop/destroy path remains available. The Host fences new child admission and
start before teardown, but retains uncertain child outcomes and the corresponding
parent charge until the provider supplies qualified containment evidence.
All consumers use the Simple Container API: Linux selects Podman; Windows
selects Windows Docker process containers. There is no engine fallback.

Container object absence, `running=false`, a zero CLI exit, helper reaping and
an empty session table are insufficient by themselves. The eventual discharge
records **parent removed, child outcome unknown**, never successful child exit.
Helper process/group/Job cleanup and storage retirement remain separate proofs.

Podman's pinned v5.2.5 implementation can retain cleanup errors while removing
the container database entry, and exec-session removal can proceed after stop
errors. Thus a subsequent successful `container exists` absence observation
does not recover the missing teardown proof. See the provider audit of
[runtime_ctr.go](https://github.com/podman-container-tools/podman/blob/v5.2.5/libpod/runtime_ctr.go#L946)
and [container_exec.go](https://github.com/podman-container-tools/podman/blob/v5.2.5/libpod/container_exec.go#L995).

## Existing mechanisms and exact gaps

| Existing source | Reusable mechanism | Missing fact |
|---|---|---|
| `providers/linux/user_mapping_v3.spl` and `oci_runtime_v1.spl` | Retained full CID/request/policy binding, independent pre/post engine inspect, live primary association | Lifetime containment of all exec descendants |
| `runtime_workspace_user_observation_linux_private.h` | pidfd before numeric proc lookup; retained proc/user namespace identity; current cgroup path matching | Pinned cgroup descriptor/device/inode, PID/cgroup namespace identity and population |
| `io/linux_container_user_observation_v1.spl` | Kind-tagged existing registry, bounded facts, generation/origin checks and retained cleanup on error | Refresh requires a live primary, so cannot prove post-destroy emptiness |
| `runtime_linux_group_owner_impl.h` | Descriptor-relative `cgroup.events` read | Its helper leader-reap authority does not apply to a container workload |
| `runtime_linux_cgroup_events_private.h` | Strict bounded `populated` parser | The caller must independently qualify the exact container hierarchy |
| Existing Windows helper Job/PTY owner | Helper ownership and cleanup | It does not own or observe the process-container silo/HCS compute system |

Current Podman creation supplies resource limits, no-new-privileges and dropped
capabilities, but does not explicitly select PID/cgroup namespaces or pin the
OCI runtime implementation. Rootless mode and defaults are not evidence for
those missing guarantees. Existing started parents must not acquire a lifetime
containment claim through a retrospective metadata-only upgrade.

The provider's v5.2.5 source audit also found that `HostConfig.Cgroup` is not
populated, `Cgroups` distinguishes only default/disabled, and `OCIRuntime` is a
configured name rather than executable identity. `PidMode=private` does reflect
the OCI namespace selection, but cannot replace the missing native identity
and lifetime proof. `State.CgroupPath` may become empty after stop; capture must
therefore occur while the qualified parent is live.

## Linux provider work package

1. Define an explicit, digest-bound managed containment profile at parent
   creation. Qualify the selected OCI runtime, cgroup v2 hierarchy and PID/cgroup
   namespaces, and prohibit workload migration outside the observed hierarchy.
   Verify actual configuration; request flags alone are not observations.
2. Capture a separate read-only containment owner while the exact parent is
   live. Reuse pre-inspect/native capture/post-inspect correlation. The private
   native capture pins the primary identity only to establish the container's
   hierarchy; it does not adopt, signal, wait for or supervise an agent PID.
3. Pin the actual cgroup v2 mount and directory identity, relevant namespace
   identities and bounded event source. Resolve paths beneath a qualified mount
   using no-follow descriptor operations. Refuse cgroup v1, wrong namespace,
   wrong mount/root, changed CID/PID/cgroup association and unsupported layouts.
4. Retain this owner independently of the live user-mapping owner. A dead primary
   must not erase the cgroup observation capability. No token decoder or raw FD
   accessor may manufacture it. Reuse the existing registry with a distinct
   observation kind and its origin/generation checks; do not add a supervisor,
   reaper, scheduler or second capacity ledger.
5. After Host teardown fencing and separately authorized lifecycle effects,
   obtain qualified native emptiness and exact engine-object absence. The
   kernel documents `cgroup.events: populated=0` as absence of live processes in
   the hierarchy, including descendants. This observation is useful only when
   the retained hierarchy and its lifetime containment were established.
   [Kernel cgroup v2 documentation](https://docs.kernel.org/admin-guide/cgroup-v2.html#un-populated-notification)
6. Preserve uncertainty if events become unreadable, the mount changes or the
   group disappears. A missing path, `ENOENT` or `ENODEV` is not automatically an
   emptiness receipt. The source work must establish how a pinned, removed
   cgroup can be distinguished from an unobservable one, or retain a qualified
   pre-removal empty observation with a proven no-repopulation boundary.

Step 6 is an explicit acceptance prerequisite, not an allowed permanent omission.
Podman/runtime cleanup may remove the cgroup before a post-destroy read. Native
source semantics and real-host tests must settle this ordering before the
profile can release charges. No observer writes `cgroup.kill`, migrates tasks,
changes limits or removes a group; lifecycle mutation remains provider-owned.

An alternative version-qualified engine/OCI teardown contract can be accepted
only if its retained evidence and real-host acceptance prove the same guarantee.
It cannot be inferred from the existing CLI/absence receipt, and does not require
adding a Host process supervisor.

## Windows provider work package

The analogous subject is the actual process-container HCS/silo containment,
not the helper Job, Docker CLI process or a guessed container PID. The provider
must bind the Engine CID to a qualified native containment identity while the
parent exists, retain the observation capability, and independently establish
teardown through that exact identity after authorized lifecycle operations.
The Windows lead must identify the actual reusable HCS/native owner and supported
event/property semantics before freezing a native ABI. No such qualified port
was established by the current source inventory. Hyper-V and Linux-container
profiles are not substitutes for Windows process isolation.

## First implementation slice: retained observations

The first source slice implements capture, bounded population observation and
handle retirement independently of final discharge. Its native facade is
`std.nogc_sync_mut.io.linux_container_containment_v1`:

- `linux_container_containment_capture_v1(pid, expected_cgroup_path,
  binding_digest)` returns `LinuxContainerContainmentTurnV1`.
- `linux_container_containment_observe_v1(owner)` returns the same turn.
- `linux_container_containment_close_v1(owner)` returns
  `LinuxContainerContainmentCloseTurnV1`.

The observation turn retains `owner`, optional `snapshot`, and `error`. A partial
capture failure retains its native owner. The close turn retains optional
`owner`, actual `closed`, and independent `error`; callers cannot infer successful
retirement merely from the absence of a snapshot or an empty error string.
No decoder reconstructs the native generation or descriptor authority.

The snapshot states are **Populated** and **EmptySnapshot**. The latter means
only that the retained hierarchy reported no live members at that observation.
It is not a teardown receipt, a no-repopulation assertion, or permission to
release capacity. An unreadable, deleted, replaced or unsupported subject yields
no snapshot and retains the owner with an error. Namespace and cgroup identity
facts remain metadata; the native slot is the source of live observation.

Capture reuses the existing private PID-first mechanics, without requiring a
user-mapping owner, numeric container user or keep-id mode. Native capture checks
the live PID/start identity and its actual cgroup association, then pins the
cgroup2 mount/directory and target/observer PID and cgroup namespaces. Subsequent
observation does not require the primary to remain live. Ambiguous or unsupported
mount-root/namespace layouts refuse rather than guessing a path translation.
The native owner neither signals nor adopts the observed primary.

The provider brackets native capture with exact engine inspections. Its
association digest includes full scope/runtime/request, installed profile and
CLI baseline, actual PID/cgroup and the pre-inspection query evidence. Failed
post-inspection closes or retains the partial owner; it cannot publish a
successfully associated common observation. The complete native field layout
and bounded parser limits are frozen against the actual implementation before
common projection code is written.

## Common boundary and Host consumption

Source targets are new `common/contracts/container/containment_v1.spl` and
`nogc_async_mut/container/containment_v1.spl`, plus platform leaves. These are
reserved targets, not existing interfaces. Freeze concrete signatures only
against an implemented native owner:

- Capture returns updated Container owner plus an opaque containment owner or
  retained partial cleanup. It requires actual provider observations and the
  qualified creation profile, never a caller PID/path or copied receipt.
- Observe returns that owner on every path with populated or empty-snapshot
  metadata, or an error without a snapshot. Qualified final emptiness is a
  separate future acceptance result. Observation cannot mutate the workload or
  synthesize success from errors.
- Close retires observation handles only, with an explicit actual retirement
  fact and an independent error. Failed cleanup retains ownership.
- Qualified evidence binds backend, full scope/runtime, original parent request,
  provider and containment-profile pins, native containment identity digest,
  capture association, teardown operation and native observation time/evidence.
  Metadata encode/decode does not recreate the observation capability.

Host uses the existing operation journal and object store. It archives the
qualified evidence before committing an explicit unknown-outcome child
discharge, then settles the retained parent allocation only when all applicable
helper, workload and storage conditions are satisfied. Restart without recoverable
qualified containment identity/evidence remains uncertain; neither a reused path
nor boot-counter equality authorizes adoption.

The separate no-effect path is narrower: an exact current `admitted` child row
under the declared process-crash durability profile can prove that Host BEGIN
never occurred, because the canonical transition graph cannot revert from
execution. The actual producer must check original archive/current journal
revision and delegation ordering under the sole writer, publish a no-BEGIN
receipt, and bind its digest to cancellation. A `cancelled` label by itself is
insufficient. This path does not assert native teardown.

## Concrete source ownership

| Owner | Source targets and scope |
|---|---|
| Architecture/common | New containment contract/facade after native interfaces are reviewed; no fake positive receipt |
| Podman | New `providers/linux/containment_profile_v1.spl` and `containment_v1.spl`; additive request/profile selection in `request_v1.spl` and `request_codec_v1.spl`; creation/capture orchestration in `oci_runtime_v1.spl`; configured routing in `simple_container_adapter_v2.spl` |
| Native observation owner | New `io/linux_container_containment_v1.spl` and private containment implementation; narrow kind extension in existing `runtime_workspace_storage_v1.c/.h`; reuse strict event parser and origin checks |
| Windows | New process-container containment leaf after actual HCS/silo owner audit; no helper Job substitution |
| Host | Same-journal teardown fence, actual evidence archive/discharge validator and separate admitted-child no-effect producer |

This document introduces no native source edit, ABI, runtime test campaign or
positive capability report. The integration owner schedules the new work package
and independent review separately from closed repair campaigns.

The request selection uses a new digest/retained version while preserving exact
V1–V3 bytes. Runtime executable selection belongs to protected installed
configuration, whose explicit new version also binds enrollment/provider
identity. No request supplies a runtime path. The source package does not edit
the capped `engine_exec_owner_v3.spl` or `engine_exec_record_v3.spl` repair.

## Acceptance gates before effect enablement and charge release

1. Actual selected engine/profile and full runtime identity are verified; wrong
   platform, namespace, hierarchy, runtime pin or unknown backend refuses.
2. A real descendant exec remains running after its direct command/helper exits;
   the observer reports populated and Host retains the charge.
3. Engine-object absence following a failed teardown cannot pass the native
   emptiness check or discharge an unknown child.
4. Actual qualified teardown produces evidence for the exact retained group or
   silo, including the runtime-removes-group ordering. Path/inode reuse and an
   unrelated empty group fail.
5. Capture/observe/close failures, fork/origin mismatch, stale/cross-kind tokens
   and interrupted publication retain the appropriate owners and uncertainty.
6. Cleanup fencing prevents a new exec/start from repopulating the subject across
   observation and commit. No stream/helper proof substitutes for this boundary.
7. Crash recovery cannot replay a child success or release without the archived
   qualified proof. Native PIDs/tokens are never deserialized as authority.
8. A valid discharge records unknown/cancelled outcome, not successful exit;
   native observation cleanup does not itself free capacity.

All gates are **NOT_RUN**. Existing native component checks and authored common
exec scenarios are not evidence for this new capability.
