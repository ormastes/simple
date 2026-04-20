# SOSIX Process And Scheduler Guide

SimpleOS process code is split into two public layers:

- `os.sosix.*` is the Simple-native OS interface. It is async-first,
  capability-oriented, and uses immutable data plus bounded queues for process
  cooperation.
- `os.posix.*` is compatibility. POSIX wrappers may block, translate errno
  values, and preserve familiar names, but new kernel, driver, service, and
  Simple application logic should use SOSIX directly.

## Scheduler Model

The kernel scheduler is implemented in `src/os/kernel/scheduler/scheduler.spl`.
It uses per-CPU run queues with scheduler-class lanes:

1. deadline
2. fixed-priority realtime
3. fair
4. background
5. idle

The compatibility `schedule()` entry point schedules CPU 0. SMP-aware callers
can use `schedule_on_cpu(cpu)`. `rebalance_once()` is the current topology hook:
it moves one fair/background task from the busiest run queue to an
affinity-compatible lower-load CPU.

Fair/background scheduling uses EEVDF-like metadata:

- `weight`
- `vruntime`
- `lag`
- `requested_slice_ns`
- `virtual_deadline`

Deadline scheduling is admitted explicitly through `admit_deadline(...)` or the
`schedctl` admission operation. Directly setting deadline metadata is rejected
because deadline tasks need budget validation and per-CPU bandwidth checks.

## Process Lifecycle

The main process lifecycle paths are:

| Operation | Kernel path | Notes |
|-----------|-------------|-------|
| `fork` | `Scheduler.clone_task` | Clones task metadata and register state. Real user address spaces use COW clone. Child `rax` is set to 0. |
| `execve` | `Scheduler.exec_image` | Builds a new user image, maps PT_LOAD segments and stack, swaps address space, and increments isolation generation. |
| `waitpid` | `Scheduler.wait_for_collect` | Collects zombie child status, supports any-child and WNOHANG, and releases child address space. |
| `exit` | `Scheduler.exit_task_by_id` | Marks zombie, closes process FDs, and wakes parents blocked on child exit. |

FD inheritance and close-on-exec live in `src/os/posix/fd_table.spl` and are
invoked by syscall dispatch:

- `fork` calls `fd_prepare_fork_to_task(child.id)`.
- `execve` calls close-on-exec cleanup only after image replacement succeeds.
- `exit` and `waitpid` close or reap process-owned descriptor state.

## SOSIX Process API

`src/os/sosix/process.spl` exposes async request handles:

- `sosix_process_fork`
- `sosix_process_execve`
- `sosix_process_spawn`
- `sosix_process_waitpid`
- `sosix_process_getpid`
- `sosix_process_signal`
- `sosix_process_exit`
- `sosix_process_wait_request`

The POSIX async process module forwards to this SOSIX surface. `wait_request`
is the explicit blocking boundary.

## Immutable Sharing

`src/os/sosix/share.spl` exposes immutable datasets and bounded queues:

- Create a dataset with `sosix_dataset_create(size, flags)`.
- Write bytes while it is unsealed.
- Seal it with `sosix_dataset_seal(handle)`.
- Share the sealed handle through a queue message.
- Receive the queue message and read sealed bytes.

Handles encode `generation << 16 | slot`. The first slot in generation 0 is
still handle `0`, but a full close followed by slot reuse returns a new
generation and stale handles fail validation. Slot and generation metadata are
available through the SOSIX and kernel queue/dataset helpers for diagnostics
and tests.

Unsealed, stale, and invalid dataset attachments are rejected. Queue capacity
and message size are bounded so the first kernel implementation can remain
deterministic. Queue poll reports read, write, and hangup readiness; blocking
wakeups are not wired here because scheduler wait queues are outside the
sharing manager.

Kernel syscall IDs 120-131 mirror the same model:

| ID | Operation |
|----|-----------|
| 120 | dataset create |
| 121 | dataset create from file |
| 122 | dataset write |
| 123 | dataset seal |
| 124 | dataset map |
| 125 | dataset unmap |
| 126 | dataset close |
| 127 | queue create |
| 128 | queue send |
| 129 | queue receive |
| 130 | queue poll |
| 131 | queue close |

## Current Scheduler And Sharing Semantics

The implemented slice now covers the scheduler/process behavior needed by
SOSIX process isolation tests:

- Scheduler topology has typed CPU entries plus flat fallback, synthetic
  SMT/cache/NUMA domain construction for tests, and x86_64 CPUID topology
  probing during early arch init.
- Rebalancing includes explicit rebalance, idle-pull balancing, wake-affine
  placement, per-CPU current mirrors, and wakeup preemption metadata.
- Fair scheduling keeps virtual-deadline ordering and tick accounting.
- Realtime scheduling has fixed-priority lanes, per-CPU RT bandwidth
  throttling, and scheduler-owned priority-inheritance mutex helpers.
- Deadline scheduling validates budget tuples, accounts CBS runtime, replenishes
  budget by period, and records overrun/miss trace events.
- `execve` copies argv/envp vectors through reusable VMM copy-in helpers before
  `build_user_process_image`.
- `dataset_create_from_file` snapshots exact fd bytes at `(offset, len)` into a
  sealed immutable dataset, restoring the open-file-description offset and
  closing the dataset builder on failure.

## Verification

Focused specs:

```bash
bin/simple test test/unit/os/kernel/scheduler/scheduler_spec.spl
bin/simple test test/unit/os/kernel/scheduler/topology_spec.spl
bin/simple test test/unit/os/kernel/memory/vmm_copyin_spec.spl
bin/simple test test/unit/os/sosix/process_spec.spl
bin/simple test test/unit/os/sosix/share_spec.spl
bin/simple test test/unit/os/kernel/ipc/syscall_sosix_share_spec.spl
bin/simple test test/unit/os/posix/process_async_spec.spl
bin/simple test test/unit/os/kernel/ipc/syscall_fd_spec.spl
```
