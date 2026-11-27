# Installed Linux fresh-epoch lower producer

Status: AUTHORED_NOT_RUN. Selected source topology B; no host provisioning,
native execution, compiler check, Podman execution or enforcement qualification
has been performed. This extends the selected fresh-provider-epoch design; it
does not replace the rootless XFS quota blocker or authorize its broker.

## Supported deployment and trust

One administrator creates a dedicated nonroot service UID/GID, nologin account
with `/nonexistent` home, disjoint exact subordinate-ID ranges, root-controlled
Host system service, cgroup2 partition and new private provider graph/runtime
directories. The Host uses the explicit `vfs` storage driver and `cgroupfs`
manager. The graph filesystem must actually be ext4 or XFS; the runtime root may
also be tmpfs. Both are owned by the service UID with exact mode0700; every
ordinary ancestor is root-owned without group/other write permission. The same
rule protects the existing fixed machine state/WAL/objects directories.

The administrator and dedicated Host service code are trusted. Concurrent
authorized root reconfiguration and hostile compromise of that same Host UID
are outside this first model. Agent containment and the upper actual process
creator must prevent guest access to the Host policy/parents and migration
routes. This is not a blanket claim about arbitrary host mounts or clients.

The actual process is the main PID of the configured root-owned system service,
with no control PID, no dynamic user, exact numeric Group setting, Delegate=yes,
and actual membership in its configured `/supervisor` subgroup. Native process
origin, credentials, namespace/maps and boot/incarnation checks come from the
landed machine reader/origin guard. `ControlGroup` is read on the Service
interface; generic unit state and fragment path use the Unit interface.

The configured provider service and activation socket must already be loaded,
persistently root-masked to `/dev/null`, inactive, jobless and never started in
the current manager. The dedicated user manager must be persistently masked;
an accessible `/run/user/UID/bus` is refused and `/nonexistent` must actually be absent, closing the default per-user configuration route. A full bounded genuine procfs PID
census, with pidfd liveness and same-procfs device/mount-ID checks, rejects any
other process with that real/effective/saved/filesystem service UID or any installed subordinate UID during preparation. A separate bounded retained cgroup2 descendant walk parses every actual cgroup.procs; only the actual Host PID in the exact supervisor is allowed. Unknown UIDs and threaded descendants refuse. The read-only population helper duplicates the internally borrowed partition FD, owns only its duplicates/children and returns root-identity data; the genuine native parent compares its own retained identity and rechecks actual context before/after.
No LoadUnit, MaskUnitFiles, Reload, StartUnit, StopUnit or signal is issued.
Existing RefUnit is used only for the installed activation socket. A missing or
unloaded provider unit refuses instead of activating it to obtain observations.

## Fixed installed profile

`LinuxMachinePolicyOwnerV1.read_fresh_epoch_profile_v1()` reads only
`/etc/simple/container/fresh-epoch-profile.sdn`, retaining its no-follow child
descriptor and exact hash under the existing root-owned policy ancestry.
Mode0644/0444 and UID0 are required. It is lazy and does not change ordinary
reader prerequisites. The strict canonical SDN schema has exactly34 fields:

| Group | Mandatory fields |
|---|---|
| Schema and epoch | kind, version, epochId, machinePolicyDigest |
| Account | serviceName, serviceUid, serviceGid, subuidStart, subuidCount, subgidStart, subgidCount |
| Manager | hostUnit, providerUnit, providerSocketUnit |
| Cgroup | partitionCgroup, delegatedCgroup, supervisorCgroup |
| Budget | partitionCpuMillis, partitionMemoryBytes, reservedCpuMillis, reservedMemoryBytes, outsideCpuMillis, outsideMemoryBytes |
| Provider | providerExecutable, providerExecutableSha256, providerPolicyDigest |
| Stores | graphRoot, runRoot, staticRoot, endpointPath, storageDriver, cgroupManager |
| Broker | brokerExecutable, brokerExecutableSha256 |

`kind=linux-fresh-provider-epoch`, version1, vfs/cgroupfs are mandatory. Catalog
and endpoint locations are derived exactly as graphRoot/libpod and
runRoot/podman.sock. Stores cannot overlap each other or the policy, machine
state, proc, sys or dev trees. Pure engine metadata comparison binds expected
UID, executable, graph/run roots, vfs and zero storage options to the exact
machine-policy provider bytes. Decoding metadata never constructs custody.

## Native custody and lifecycle

Each native descriptor enters canonical cleanup ownership before a fallible
statx, filesystem query, read, hash or proc observation. Namespace/process
origin is checked before every canonical registry access and close. Root-owned
binary descriptors and exact SHA256 are retained with size/ctime/mtime identity; actual security.capability must be absent on both pinned provider/broker binaries (ENODATA or filesystem unsupported only), checked with retained fgetxattr rather than inferred from current Host caps0;
directory identity deliberately excludes mutable size/timestamps. The procfs
census is bounded at65536 tasks, owner slots at4096, and each executable hash at
256MiB. The population walk is bounded to128 cgroup directories (384 retained entries), depth16 and512 entries per directory. Unsupported ABI, truncated or unavailable evidence refuses.

The parent cgroup must actually be cgroup2 domain mode with cpu/memory delegation,
finite exact cpu.max and memory.max, zero memory.swap.max and no tighter
ancestor limit. Every ancestor outside delegation retains root-owned,
non-group/world-writable cgroup.procs and controller files. This implements the
kernel's common-ancestor migration-write boundary for a caps-zero service.
Installed outside charge plus partition must fit both actual physical totals
and machine allocation. Reserved Host/provider overhead is included inside the
partition; usable is partition minus reserved. GPU/exclusive CPU/storage quota
and bind mounts receive no grant.

The composite zero-argument factory returns Rejected, CleanupRequired(owner,
reason) or Ready(preparation). It retains the genuine installed readers, native
FD owner, authenticated system-manager bus and fixed state-relative epoch lock.
The lock key derives from actual partition/store identities, not caller metadata.
Preparation current rechecks real manager/native evidence and empty graph/run
roots. It does not require machine WAL emptiness after the upper first commit.

`consume_preparation_v1()` atomically changes the same canonical owner phase;
all copied preparation aliases lose current/transition rights before a successor
is returned. Exact original handles and lock remain held. It supplies supporting
custody only: no first-charge receipt, admission, process spawn or journal owner
is created. The upper must separately retain genuine durable admission and its
same machine writer. Successor current permits populated provider stores while
checking retained identities, topology and partition limits. Closing a consumed
preparation alias cannot close its live successor.

All close outcomes retain pending owners; the first cleanup diagnostic is sticky.
Released or conclusively consumed-error components are cleared once. Native
Linux close is consumed before the call and is never retried by numeric FD;
generic stale/unknown lock or parent results remain pending. Process-origin
refusal performs no close in an inherited fork child.

## Launch data projection

The successor bind/validate ports recheck genuine custody, actual reserved
supervisor cgroup limits/dev/inode/generation and the full inherited Host
environment. The inherited broker environment is bounded and accepts only the
documented fixed PATH/HOME/SHELL, service USER/LOGNAME, C locale, pinned runtime
directory and bounded systemd invocation/journal metadata. Unknown keys refuse;
empty child environment does not sanitize the broker. Concurrent trusted Host
environment mutation is outside this synchronous profile.

Projection derives provider/broker binaries and hashes, empty child environment
and inputs, exact runtime working directory, root/runroot/vfs/cgroupfs flags,
enforced delegated/helper cgroups and image mode. Requested helper resources
must fit usable capacity. Creation derives cgroup-parent, enabled cgroups, bounded CPU/memory limits,
cap-drop ALL, no-new-privileges and network none; caller override, host mount,
device, privileged, alternate-engine and namespace flags refuse. Only a bounded
operation set is supported. Projection preserves the upper request's bounded
metadata/deadline/transport slots so that the upper can durably bind the exact
normalized template and stamp its local one-shot permit. This is DATA; only the
upper actual creator holding durable admission plus this same successor may
invoke the existing profiled process producer. Actual resulting workload
ancestry/enforcement remains a required upper/native fixture assertion.

## Same-writer initial history

Only the Linux platform storage adds record-only fresh_epoch_head_v1(record)
and fresh_epoch_commit_v1(record); the neutral proof-bearing facade and upper
admission are separate ownership. Generic missing-CURRENT and empty-parent
commit refusal remain unchanged. The helper is strictly read-only and exposes no publication, initialization or reset method. The sole initial publication is private inside the original machine-storage owner, behind its actual retained writer/binding and canonical one-shot eligibility. It introduces no journal, daemon, writer reacquisition, arbitrary entries port or new runtime export.

The platform independently binds exact installed policy/profile, principal,
provider policy/identity, physical budget and its own retained root identities.
Native store digest includes graph/run and the actual fixed state/WAL/objects
directory IDs in the frozen hash framing. Temporary inventory descriptors are
canonical owners retained through every error. Initial enumeration permits only
the installed empty objects directory: orphan records, staging directories,
unknown names and even a leftover commit.lock refuse.

`binding_created_here` becomes true only after this exact held writer's actual
exclusive machine binding publication and winner readback. Observational heads
do not consume it. Existing binding plus missing CURRENT always refuses,
including a crash after binding before commit. Commit consumes the private flag
before backend mutation, writes exactly the pure codec's four rows using the
actual clock and existing backend CAS, then reads back/replays the exact result.
Ambiguity quarantines the writer and may require explicit operator repair;
there is no automatic initialization retry. Existing history is walked through
a bounded contiguous immutable chain to the original four rows, replays the
original record exactly, and compares its stable installed binding. Historical
process/manager/generation fields are not required to equal the current process.
The upper currently refuses reopening a history with creator descendants; this
reader's bounded data replay does not mint a reusable spawn permit.

## Evidence and dependencies

The authored fixture exercises real supported provisioning, actual lock
contention, alias/phase/close behavior, actual native nonemptiness refusal and
strict pure metadata negatives. Three separately provisioned real negative specs require exact native subordinate-UID-occupant, unknown partition-occupant and executable-capability refusals; unrelated missing prerequisites cannot pass them. None has run. PID namespace/fork, proc bind
mounts, mask/manager replacement, cleanup faults, crash/CAS/orphans, actual
Podman/workload ancestry and resource pressure are NOT_COVERED by a run.
No compiler/link/stdlib/MCP checks were executed because the admitted runtime
is unavailable and the shared native campaign budget is exhausted.

Dependencies are the landed Linux machine/origin/retained/file-lock/WAL ports,
the upper-owned pure machine_fresh_epoch_record_v1 codec, and exact supervisor
typed boolean/u64-property readers from the separately frozen R3 bus bundle.
No acceptance of pending native foundations or transport/authentication work
is implied. Independent review and later native qualification are required.

Primary references: [kernel cgroup2 migration and resource controls](https://www.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html),
[systemd D-Bus interfaces](https://www.freedesktop.org/software/systemd/man/256/org.freedesktop.systemd1.html),
[Podman root/runroot/cgroup options](https://docs.podman.io/en/latest/markdown/podman.1.html).
