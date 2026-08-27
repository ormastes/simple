<!-- codex-design -->

# SimpleOS Enhancement Architecture

## Decision

SimpleOS has one execution-security architecture. A manifest/profile is policy
input; `CompiledExecutionPolicy` is its trusted compilation result; typed
object capabilities are the kernel's runtime authorization mechanism.

```text
role / manifest / session policy
             ↓ compile
CompiledExecutionPolicy → SpawnSpec → Job + CSpace + TCB
                                         ↓
KernelCallContext → syscall → typed object-handle check → operation
```

## Capsule boundaries

- **Kernel security capsule:** owns principals, jobs, CSpaces, caller context,
  capability lineage/revocation, and the sole process creation path.
- **Isolation capsule:** owns only visibility and namespace views; it cannot
  grant an object capability.
- **Resource capsule:** owns hierarchical admission/accounting and cannot
  grant authority.
- **Workload capsule:** owns manifest validation, policy compilation, service
  dependency/lifecycle, and fresh-grant reacquisition.
- **Broker capsule:** owns secret/model/tool/egress/approval material outside
  agent and container workloads.

## Key invariants

1. A security-sensitive call has an immutable context associated with a live
   TCB; scalar IDs are not authorization inputs.
2. `child authority ⊆ parent delegable authority`; exec/fork never increase it.
3. A handle checks object type, right, and generation.
4. `restarted_workload.old_grants = ∅` before the new process receives grants.
5. Namespace/filter/resource policy only restricts; it never authorizes absent
   an object capability.
6. A managed workload is bound once to a nonzero process-view domain before it
   may run; a conflicting rebind is rejected.
7. `KernelCallContext` identity, job, CSpace, resource, and audit fields come
   from persistent TCB bindings, never reconstructed from a role string or
   capability-generation counter.
8. A nonempty managed `SpawnSpec.image_hash` is a BLAKE3 content address and
   must match the exact bytes parsed into the child image before CSpace minting.
9. Root mint authority is kernel-owned, bound only to the live PID1 reaper,
   non-transferable through CSpace/IPC/fork, and cleared before task exit.
10. A job's termination/revocation recursively affects its descendants.

## Pattern choice

The selected pattern is composition, not separate service/container/agent
security stacks: each is a specialization of `WorkloadManifest` plus a job,
CSpace, optional isolation domain, resource domain, identity, and lifecycle
monitor. This is a virtual-capsule boundary: no MDSOC feature transform is
needed until all existing spawn paths are unified.

The scheduler owns the one transitional orphan-adoption rule. Once the
filesystem-backed PID1 launch has successfully installed its TCB, that PID is
the configured reaper. Exiting a task atomically reparents each direct child to
that reaper before the task is left as a zombie. If the configured reaper
itself exits, its children fall back to kernel task 0 and task 0 becomes the
future adoption target. A zombie cannot be installed as reaper. This preserves
a live parent for exit-status collection without making a dead service an
authority source; cross-domain observation remains restricted separately.

Managed spawn binds authority, resource accounting, and lifecycle ownership to
the same live caller: `KernelCallContext.task_id` must equal the scheduler's
current task before child-budget admission, CSpace minting, or TCB creation.
That prevents one task's pouch from being minted while a different task is
charged as parent and given supervisory visibility.

The resulting managed-child binding has a fresh principal, CSpace, job,
resource-domain, and audit identity. It records the caller's job/resource
domains as parent lineage rather than sharing them, so each service or agent
instance is independently terminable and accountable. The scheduler accepts
that binding once only, before the child is exposed; a second bind or invalid
trusted binding fails. This is the live foundation for hierarchical
termination/accounting, pending stable non-PID-backed domain allocation.

`ResourceBudget.process_limit` is installed on the *new managed child* as a
descendant admission ceiling, then checked when that child later launches
workloads. It therefore cannot accidentally charge PID1's direct-service
count. The same one-time binding installs the memory-page ceiling in the child
isolation profile; CPU, I/O, and network controllers remain active work.

A nonempty policy syscall allowlist is also installed once on the managed TCB
and inherited by fork. Both syscall dispatch variants consult it before their
normal capability/handler logic, so it can only reduce the kernel attack
surface. A `WorkloadManifest` without an explicit nonempty allowlist is rejected
at compilation, so typed services, containers, and agents cannot silently opt
out of this enforcement plane.

The scheduler now has a trusted `terminate_job` lifecycle primitive. It first
captures live members of the selected job and its descendant-job lineage, then
exits each through normal cleanup/reparent logic, and will not terminate kernel
bootstrap job 0. It provides the kernel mechanism for session revocation,
service teardown, and agent emergency stop; typed job handles and a userspace
invocation path remain future work.

If a terminated job contains the CPU-0 current task, the scheduler first moves
the current sentinel away from that zombie and immediately chooses the next
ready task. Multi-CPU stop/IPI coordination remains part of the later resource
and scheduler-control lane.

Every scheduler exit now replaces the zombie's task CSpace with pledged
deny-all authority and advances its capability generation before retaining exit
status. This covers signal and job-termination paths that do not receive an
IPC capability manager. The normal syscall-exit path additionally revokes IPC
manager records and closes descriptors.

Shell PATH resolution is now a pure candidate-name operation. It never probes
global VFS state; `shell_exec_as` presents each candidate to the gated spawn
path and only continues after a normal not-found result. This removes the
shell-side filesystem discovery bypass, while the broader caller-aware VFS
migration remains active.

The old scalar shell/loader bridge is bootstrap compatibility only. Once PID1
commits authority it rejects every caller, including task 0, because a numeric
caller ID cannot prove ownership of the live parent CSpace. Scheduled shell
execution must use the context-bound spawn syscall path.

The PID1 handoff uses a stricter seal than the legacy boot compatibility seal:
after PID1's explicit CSpace exists, ambient `CapabilitySet.full()` spawning is
denied for every caller, including task 0. Any continued service creation must
use the managed CSpace mint path. The generic compatibility seal remains only
for older boot flows that have not reached this handoff.

`managed_workload_launch` is the typed PID1-to-kernel transition. It accepts a
`CompiledExecutionPolicy`, rechecks that its identity, image, and `SpawnSpec`
agree, parses the supplied executable bytes, and invokes the sole explicit
CSpace spawn seam. It has no role-text or ambient-capability input. A future
ring-3 ABI must reach this function only after the service manager verifies a
signed manifest and resolves trusted executable bytes.

The P0 C ABI process and IPC shims now enter `syscall_handler_ipc_state` rather
than calling process or IPC leaves directly. That dispatcher applies the
immutable syscall filter and checks the live current TCB CSpace for process and
IPC authority. File, network, and device shim families still require the same
central-dispatch migration; they are tracked as an open whole-syscall-surface
gap rather than covered by this narrow routing change.

### Live CSpace delegation follow-up — 2026-08-11

The stateful `CapGrant` ABI now takes `(target_task_id, source_token_id)` and
delegates only that exact token through the scheduler-owned TCB CSpaces. The
recipient receives a fresh token with a new ID, `parent_token_id` set to the
source, one less delegation depth, a re-bound owner, and a new CSpace
generation. Unknown, foreign, zero-depth, self-targeted, absent, and counter-
overflow transfers fail without mutation. The former value-only handler now
returns an error instead of synthesizing `ProcessSpawn` in the disconnected
`IpcManager` capability ledger. `os.userlib.security.cap_grant` consequently
accepts a source token ID rather than a caller-controlled capability name.

This remains **source-checked but not interpreter-verified**: the focused
`cspace_transfer_spec` run stops while parsing the shared
`scheduler_task_mgmt.spl` with `expected identifier, found Dot` and no source
location. Three bounded diagnose/fix attempts did not produce a runnable
spec. The target-native build is separately unavailable because the available
self-host compiler candidates crash during their environment-write probe.
Neither condition is evidence that live delegation works at runtime.

Update: the parser fault was isolated to authority bodies embedded in the
large scheduler lifecycle module and removed by moving isolation, revocation,
and child-accounting operations into `scheduler/authority_runtime.spl`; live
delegation lives in `scheduler/cspace_delegation.spl`. A reserved local name
`bind` in the owned-IPC `NET_BIND` authorization path was also renamed to
`bind_request`, restoring parser reachability of the main syscall module.
The focused delegation spec now exits successfully, though this runner emits
no compact pass summary. The revocation spec reaches execution but currently
has one failing example out of two, so revocation remains unverified. Direct
module compilation still reaches an unrelated `undefined identifier: self`
semantic diagnostic after parsing, and native/QEMU evidence remains blocked.

Container runtime follow-up: `ContainerRuntime` now reconciles a bound task's
actual scheduler `Zombie` transition before posting the existing monitor
observation. It rejects absent and still-running tasks, so a container model
cannot fabricate a process exit merely by calling `post_monitor_report`. The
manager still owns capability/view teardown and restart policy. A kernel exit-
notification endpoint remains the required replacement for this bounded poll
bridge in the production event path.

Agent runtime follow-up: a controller can now emergency-stop a launched agent
only when its live job is an ancestor of the target agent job. The helper
delegates the actual recursive transition to `Scheduler.terminate_job`, so the
agent's subagent jobs exit through the same CSpace-clearing lifecycle path.
It rejects self-termination and sibling/unrelated job targets by PID.
