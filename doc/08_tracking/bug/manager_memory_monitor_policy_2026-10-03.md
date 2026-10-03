# Manager memory reservation was also an execution cutoff

The generic Linux and Windows workers passed the task's positive capacity charge
directly to cgroup `memory.max` and Job memory limits. A compiler requiring more
memory could therefore be terminated even when the requested policy was to observe
memory without imposing a compiler cutoff.

`BuildTaskV1.memory_policy` now accepts `enforce` (the legacy default) and `monitor`.
Both require a positive, bounded `memory_limit_bytes` capacity reservation. Monitor
passes zero only to the native enforcement argument; it never fabricates host
capacity or removes reservations. Task identity binds the policy. Legacy enforce
task/run wires retain their old encoding, while monitor uses TASK-4/RUN-5 and old
workers reject those versions. Mixed runs retain each task's policy.

The Linux owner creates the same cgroup and keeps pidfd/tree control and cleanup.
Monitor installs and reads back `memory.max=max` and `memory.swap.max=max`.
Existing enclosing cgroup or host limits still apply. Windows retains its Job and
kill-on-close behavior and verifies that the memory-limit flag is absent. Native
Linux work timeout zero disables its work deadline; cancellation/reaping remain.
Zero-work-deadline support in the generic process observation owner is a separate,
coordinated deadline change.

Workers write a task-bound `compiler.memory` receipt after authoritative reap.
It distinguishes requested policy, positive reserved bytes, effective enforcement,
enforced bytes and observed peak with its actual metric. Job commit peak, cgroup
memory peak, process-tree peak and direct-child RSS are not interchangeable.
The generic process-group worker has no memory enforcement provider and now refuses
an `enforce` task instead of silently executing it without a cap. Monitor works
with its native direct-child RSS evidence even when whole-tree accounting is absent.
The pre-spawn refusal writes a typed no-child certificate and `no-parent-owned`
settlement; the manager also requires the matching ERROR result before releasing
the reservation. Successful or cancelled process-group cleanup writes settlement
only after authoritative reap. It never fabricates a reap for a rejected child.

Grouped native contracts/brokers and managed manifest flag forwarding are owned by
parallel changes; this patch alone is not a complete managed deployment. This is a
policy correction, not a fix for a compiler leak or a guarantee against host OOM.

Acceptance fixtures: `memory_policy_spec.spl` checks codec/identity, positive
reservation, mixed runs, provider metrics and false enforcement receipts. The
Linux native capacity fixture adds `monitor` mode checking real cgroup readback,
zero work deadline, peak and cleanup. `windows_memory_policy_main.spl` exercises
real Jobs in enforce and monitor modes with trivial children and finite probe
cleanup. SPL/native execution is **UNRUN** pending admitted platform qualification;
no full compiler or VM was launched for this change.
