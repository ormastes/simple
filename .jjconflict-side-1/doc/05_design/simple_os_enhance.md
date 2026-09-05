<!-- codex-design -->

# SimpleOS Enhancement Detail Design

## Phase 0 algorithm

1. At syscall dispatch, resolve the executing `TaskControlBlock` exactly once.
2. Construct immutable `KernelCallContext` from TCB-owned principal, job,
   CSpace, isolation, resource, and audit IDs.
3. Pass that context through syscall/spawn/exec helpers.
4. At filesystem exec, obtain the caller capability set from that same live
   TCB; reject unresolved callers instead of using ambient authority.
5. Retain an authority-computation trace that records parent authority,
   policy ceilings, requested authority, and the child result.

The Phase 0 implementation reaches the shared `_handle_exec_state` handler:
it reads the scheduled current TCB, adapts its current capability pouch to a
`KernelCallContext`, and runs the context gate after bounded path copying but
before grant/image work. This covers the direct C ABI exec shim, which otherwise
bypasses the model syscall dispatcher.

The shared raw-entry, binary-entry, and direct-binary spawn handlers now also
derive a context from the scheduled TCB for a migrated recipe. Their child
CSpace mint therefore receives the live parent pouch, rather than a synthetic
recipe-shaped seed. The synthetic seed is retained only when no current TCB
exists, which is the explicit kernel-origin bootstrap seam. A regression case
pins the fail-closed result: an empty live parent can create a child only with
an empty pledged pouch, never with the recipe's requested grants.

The filesystem loader now has a non-bootstrap registration seam:
`fs_exec_register_image_into_scheduler` accepts an explicit context, recipe,
validated image, priority, and scheduler. It checks the context before mutation
and writes the child into that supplied scheduler with a CSpace minted from the
same context. The binary-spawn syscall consumes this seam, so it no longer owns
a duplicate `create_user_task_pid` branch. The old `fs_exec_prepare_spawn_*`
family remains a compatibility bridge and still requires retirement before a
filesystem-backed PID1 can be the normal boot path.

The C ABI process, fork/exec, and IPC entry shims now use
`syscall_handler_ipc_state` and adopt both returned scheduler and IPC state.
For these syscall classes, authorization is read from the scheduler's current
TCB CSpace, not from an independently populated IPC capability record. The
remaining ABI shim families are not yet uniformly routed and remain an
explicitly tracked enforcement boundary.

`InitService` is now the first runtime consumer of the typed service lifecycle:
registration creates a `ServiceManifest`; a service declaring required grants
fails closed until a broker is injected; every terminal transition revokes held
grant handles; and every restart runs `on_restart()` before a broker reacquires
fresh handles. The manager also exposes a dependency-ordered boot transaction
and reverse-order shutdown. It is not yet wired as filesystem-backed PID1;
that requires the remaining live scheduler/boot handoff work.

The filesystem syscall lane now resolves a raw path before authorization and
asks `file_access` to evaluate the exact canonical object against the same
`KernelCallContext` used by process creation. Open distinguishes read, write,
truncate, and create authority. A successful FAT32 open records that canonical
path with the task-scoped descriptor; subsequent FAT32 reads and writes fetch
it and re-check the live CSpace. This prevents a capability revoked or
attenuated after open from becoming a permanently ambient file grant. The
kernel-origin task-0 exception is explicit; a missing nonzero TCB produces an
empty, deny-all context. Direct handlers also activate the caller's
task-scoped descriptor table before descriptor lookup or allocation. Generic
legacy POSIX descriptor backends remain an open migration item because they do
not preserve a capability-addressable opened object. Process exit clears every
FAT32 descriptor/path record for the exiting task after backend close, avoiding
stale object metadata across task-ID reuse. The file gate additionally requires
each concrete token's owner to equal the context task, so a non-kernel ambient
`CapabilitySet.full()` (which has no tokens) cannot authorize filesystem use.

PID1 preparation is now a real live-scheduler transition rather than the old
per-launch bootstrap scheduler: `/system/service_manager.smf` is built through
the shared fs-exec seam with the explicit `service-manager` recipe and concrete
FileRead(`/system/`), FileExec(`/system/`), and ProcessSpawn seed tokens. The
scheduler retags those delegated tokens to the returned child PID before its
TCB is installed. RV64 boot installs the trap runtime, prepares PID1 in that
same trap-owned scheduler, seals ambient spawning, then invokes the existing
ring-3 handoff. This is
not yet system-test proof: no repository build/image route currently produces
or stages `/system/service_manager.smf`; image production plus QEMU evidence
are required before the old inline HTTP fallback can be retired.

At this PID1-specific handoff, the seal denies ambient spawning to *all*
callers, including task 0. PID1 needs no exception because it already has
concrete `FileRead`, `FileExec`, and `ProcessSpawn` tokens. Older boot code's
root-compatible seal is deliberately not used by this path.

After a successful PID1 preparation, the scheduler records that task as its
reaper. Task exit reparents direct children before the exiting task remains a
zombie, and an exiting reaper's children fall back to task 0; task 0 then
becomes the future adoption target and a zombie cannot be reinstalled. The
adopted child can be exited and collected through normal `wait_for` by the new
parent. This is scheduler lifecycle plumbing only: it does not claim a booted
userspace supervisor until the target service-manager artifact and
manifest/spawn syscall ABI exist.

The shared live scheduler seam now also exposes explicit `SpawnSpec` launch.
It checks the caller's real `FileExec` and owned, delegable `ProcessSpawn`
tokens, mints the child CSpace directly from that pouch, and rejects the entire
launch if any requested grant cannot be minted. This prevents the prior unsafe
state where a partially minted service could still execute. It also requires
the context task to equal the live scheduler current task before it charges a
child budget or creates a TCB, eliminating a cross-task authority/accounting
confused deputy. The still-missing userspace manifest syscall must marshal only
verified `SpawnSpec` data into this seam; it must not recreate authority from
paths, role text, or ambient state.

`launch_compiled_workload_into_scheduler` is the kernel-facing service-manager
adapter. It rejects a policy whose image path/hash fields disagree, validates
the parsed executable, and delegates to `fs_exec_register_image_with_spawn_spec`.
That downstream gate still checks the exact bytes, caller-owned `ProcessSpawn`,
full grant minting, current-task equality, TCB binding, and isolation binding.
It is intentionally callable only as a typed kernel interface today; serializing
this policy over the ring-3 syscall ABI remains separate work.

After a successful typed launch, the kernel binds the policy's nonzero process
and memory-page limits exactly once. The process limit is enforced against the
workload's direct descendants on later managed launches, while the memory
ceiling is retained in its task isolation profile. Limit-binding failure exits
the provisional child rather than exposing a partially constrained workload.

When a compiled policy carries a nonempty `syscall_allowlist`, the launch
adapter binds it once to the child. Both the state-preserving trap dispatcher
and compatibility result-only dispatcher deny calls outside that list before
file-descriptor activation, capability checks, or handler side effects. Fork
preserves the filter; no child can widen it.

`compile_workload_manifest` rejects an empty syscall allowlist. This turns the
allowlist into an explicit policy decision rather than preserving legacy broad
syscall access by omission.

`Scheduler.terminate_job` is the corresponding trusted lifecycle operation.
It snapshots non-zombie members of the selected job and descendant jobs,
routes every exit through ordinary task cleanup and reparenting, and refuses
bootstrap job 0. It is deliberately not a generic process syscall yet: a later
typed `JobHandle` must authorize its userspace exposure.

When a job stop includes the CPU-0 current task, `terminate_job` resets that
current slot to the idle sentinel and calls the normal scheduler selection
path. This prevents a scheduler reference to a zombie; other CPUs need the
future coordinated stop/IPI implementation.

Scheduler-level exit clears the authoritative TCB CSpace before the task becomes
a zombie and advances the isolation capability generation. This ensures that
signal and job-wide termination cannot leave a zombie holding a usable live
authority pouch; syscall exit performs its additional IPC-manager revocation.

Immediately after TCB allocation the managed seam installs a one-time trusted
security binding: child principal/CSpace/job/resource/audit IDs are fresh, and
the authenticated caller's job/resource IDs are retained as parent lineage.
Binding failure exits the not-yet-exposed child. This makes each managed
workload independently controllable while preserving hierarchical termination
and accounting without allowing a manifest or userspace caller to set IDs.

Shell command lookup no longer uses a raw VFS executable-byte read as an
existence probe. The PATH helper returns ordered names only; execution submits
each to the recipe-gated launch seam, stopping on any error except ordinary
image-not-found. This avoids treating an unauthorized VFS read as command
discovery.

`src/os/services/workload/workload_manifest.spl` freezes the common typed
control-plane contract. Services, containers, and agents now have one
`WorkloadManifest` / `CompiledExecutionPolicy` representation with identity,
image binding, typed authority request, isolation view, resource budget,
lifecycle, and audit policy. Compilation validates metadata only; the kernel
still performs the authoritative parent-CSpace intersection during launch.
`InitService.register_workload()` preserves that compiled policy through both
the initial brokered launch and a restart: it revokes the prior broker handles,
reacquires new handles, and calls the typed workload launcher again. This is a
supervisor-boundary invariant, not yet a PID1-to-kernel syscall ABI.
The compiled policy also retains its `ImageSpec`; the supervisor rejects a
mutable `ServiceDef.binary` that no longer equals the policy's absolute
executable path before it asks a broker for grants. Actual bytes-to-digest
verification remains a kernel loader responsibility and is not claimed here.

The explicit managed fs-exec seam binds each newly created task to a unique,
nonzero `TaskIsolationProfile.profile_id` before returning it to the caller.
The binding is one-way: a different nonzero domain is rejected, and an
unexpected bind failure exits the new task before it can execute. This creates
a real process-view anchor for later PID/IPC/VFS gates, but those gates are not
yet comprehensively wired.

The process diagnostic/control syscall lane now consumes that anchor for task
listing, task information, signals, priority changes, and scheduler control.
Kernel task 0 is the bootstrap exception; otherwise callers see themselves,
their direct children, or tasks in their own nonzero view. The parent exception
is a lifecycle bridge for PID1 supervision and must later be replaced by typed
process/job handles so it cannot become an ambient control relationship.

Fork carries the parent process-view domain and all restrictive isolation
fields forward while assigning the child COW address space. It does not reset a
confined workload to profile zero, and forked authority remains the separate
attenuated-C-Space path.

For the live managed-spawn path, `SpawnSpec.budget` now bounds direct children
of its caller. The count includes unreaped zombies, and admission fails before
minting/creating an additional task. This is the first live PID budget gate;
hierarchical CPU, memory, I/O, and network accounting remain later work.

Every TCB now owns a `TaskSecurityBinding` for principal, job, parent-job,
CSpace, resource domain, parent-resource domain, and audit identity.
`KernelCallContext` reads the live bindings directly. Normal task creation
establishes PID-backed defaults; fork creates fresh principal/CSpace/audit IDs
while retaining the same job/resource domain. Managed launch creates fresh
job/resource domains and records the caller domains as lineage. Stable
manifest-derived domain allocation remains later policy-registry work.

The direct `execve` ABI handler now derives its authorization input through
that same persistent-TCB adapter rather than reconstructing a legacy context
from scalar metadata. Thus model-dispatched and direct syscall entry points
observe the same principal, job, CSpace, resource, and audit bindings.

`workload_image_hash` binds a nonempty managed `SpawnSpec.image_hash` to the
actual `UserProcessImage.file_bytes` using canonical `blake3:<hex>` addresses.
The loader rejects mismatch before it mints a child CSpace. PID1 now creates an
explicit verified spec from the bytes it receives. Empty image hashes remain
only for legacy named recipe compatibility and cannot satisfy a compiled
workload manifest; compilation also rejects malformed/noncanonical BLAKE3
identifiers before a policy reaches the loader.

Both FAT32 image routes now have an authoritative staging contract. The
pure-Simple bake places an explicitly supplied `SIMPLEOS_PID1_BINARY` at the
canonical path; the QEMU `make_os_disk` route verifies target ELF architecture,
wraps it as SMF, and publishes the FAT-compatible `/SYS/SVCMGR.SMF` alias that
the VFS maps back to `/system/service_manager.smf`. Its
`SIMPLEOS_REQUIRE_PID1=1` release gate rejects an absent artifact. This removes
silent image ambiguity but does not manufacture a service-manager executable:
the target-native binary build and QEMU transcript remain required evidence.

## Error policy

- Unknown task, stale generation, missing capability, or unresolved context is
  an explicit denied/error result.
- No helper may substitute `CapabilitySet.full()` or an empty allow-all set.
- Compatibility wrappers may only derive context from a live scheduler; they
  must not accept a caller-less fallback.

## Later phase lifecycle

The PID1 manager validates a manifest and image, reserves declared endpoints,
constructs the policy, creates a job/CSpace, then spawns the service. On exit it
revokes the old CSpace, releases broker grants, resets the job as policy
requires, and derives a fresh child authority for any restart.

`compile_agent_policy` is the agent control-plane specialization of this same
contract. It verifies every requested `FileRead`, `FileWrite`, `FileCreate`,
`FileExec`, or `ProcessSpawn` grant against the already-resolved profile and
its allowed roots. It retains child-depth, model-token, and tool-call budgets
beside the compiled workload policy. Profile dimensions that need dedicated
network, secret-use, UI, model, or device brokers are rejected until those
typed handles exist; they are never converted into raw credentials.
