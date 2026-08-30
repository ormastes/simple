# SimpleOS filesystem-server thread runtime bridge

## Current gate

The x86_64 filesystem-executable runtime does not yet support
`rt_thread_spawn_isolated` or `rt_thread_spawn_isolated_with_args`. Both return
the invalid handle `0`; `ThreadHandle.valid()` exposes that condition and
`join()` returns `-38` (`ENOSYS`) without entering the kernel trap stub. Server
promotion must reject a requested worker count above one when any spawn returns
an invalid handle.

This is intentionally separate from TCP. The x86_64 boot runtime already owns
a real virtio-net TCP socket table and packet path through `rt_net_socket`,
`rt_net_bind`, `rt_net_listen`, `rt_net_accept`, `rt_net_recv_bytes`,
`rt_net_send_bytes`, and `rt_net_close`. The standard `rt_io_tcp_*` ABI now
adapts to that owner. Binding is admitted only for the wildcard IPv4 forms
`0.0.0.0:PORT` and `*:PORT`; rejecting a host-specific address prevents a
loopback request from silently becoming a public listener.

## Why scheduler code cannot be called directly

The canonical `Scheduler.create_task` path owns `TaskControlBlock`, address
space, capabilities, stacks, and lifecycle state in Simple. It does not expose
a C ABI that accepts a runtime closure record, installs the child execution
context, and returns a joinable result handle. Calling its internal helpers
from `rt_extras.c` would bypass those ownership and isolation rules. The AP
trampoline is CPU bring-up, not an application-thread API.

## Required implementation

1. Add a kernel-owned `spawn_runtime_closure` port that validates a closure
   entry and immutable arguments within the caller's mapped executable.
2. Allocate a child task, stack, execution context, capability subset, and a
   generation-tagged join record through the canonical scheduler.
3. Return an opaque nonzero handle only after the task is runnable; unwind all
   allocations on partial failure.
4. Implement join, completion polling, and detach/free against the same
   generation-tagged record, including task fault and cancellation results.
5. Wire `rt_thread_available_parallelism` to admitted online CPUs only after AP
   scheduler handoff is proven; until then it truthfully returns one.
6. Add a filesystem-launched native SSpec that proves two closures execute,
   join exactly once, cannot forge handles, and leave no task/join records.
7. Only then admit multi-worker SimpleOS web/database server receipts and
   throughput comparisons. Single-worker TCP operation can be tested earlier.

No QEMU or native build evidence was produced by this audit.
