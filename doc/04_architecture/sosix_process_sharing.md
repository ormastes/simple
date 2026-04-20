<!-- codex-design -->
# SOSIX Process Sharing Architecture

## Decision

SimpleOS uses **SOSIX** as the primary Simple-native OS interface. SOSIX is
async-first, capability-oriented, and shaped around Simple language concepts
instead of POSIX process and file-descriptor assumptions. POSIX remains a
compatibility layer over SOSIX.

## Layering

```text
Simple apps / drivers / services
        |
        v
os.sosix: async process, immutable dataset, bounded queue IPC
        |
        v
kernel syscalls, IPC, scheduler, VM, capabilities
        ^
        |
os.posix: blocking compatibility wrappers for C/POSIX callers
```

New driver and OS logic should use `os.sosix.*` directly. POSIX wrappers may
block, translate errno values, and preserve POSIX names, but they should not own
new core semantics.

## Process Sharing Model

SOSIX supports process cooperation through immutable data and queue-based
coordination:

- `SosixDataset`: a bounded immutable byte dataset. Writers fill it while open,
  then seal it. Once sealed, mutation is rejected and handles can be shared.
- `SosixQueue`: a bounded MPMC message queue. Messages can carry a small payload
  plus one attached dataset handle.

This keeps shared data read-only after publication and moves synchronization to
queue operations. It avoids POSIX shared-memory aliasing as the default model.

## Invariants

- Dataset handles are stable indexes plus generation-ready metadata in later
  kernel capability wiring.
- Dataset writes are allowed only before `seal`.
- Dataset reads and queue attachments require sealed datasets.
- Queue send preserves FIFO order per queue.
- Queue receive consumes exactly one message.
- POSIX wrappers call SOSIX request APIs and block at the compatibility edge.

## Migration Plan

1. Introduce `os.sosix` modules and tests. Done for process/share/I/O.
2. Move POSIX process async wrappers onto `os.sosix.process`. Done.
3. Add immutable dataset and MPMC queue APIs under `os.sosix.share`. Done.
4. Move async I/O ownership from `os.posix.async_io` into `os.sosix.io`.
   Done; POSIX keeps forwarding wrappers.
5. Wire dataset/queue handles into kernel capability and VM mapping syscalls.
   Done for fixed-table kernel managers and syscall IDs 120-131.
6. Follow-up: migrate socket and dylib async ownership into SOSIX, then add
   VFS-backed dataset byte population for `dataset_create_from_file`.

## Current Coverage And Remaining Work

Implemented source paths:

- `src/os/sosix/process.spl`: async-first process request slots for fork,
  execve, spawn, waitpid, getpid, signal, and exit.
- `src/os/sosix/share.spl`: immutable dataset builders and bounded queue IPC.
- `src/os/sosix/io.spl`: native async I/O requests, with POSIX forwarding wrappers.
- `src/os/kernel/ipc/shared_dataset.spl` and
  `src/os/kernel/ipc/process_queue.spl`: kernel fixed-table managers backing
  syscall IDs 120-131.

Remaining SOSIX logic is intentionally explicit:

- `dataset_create_from_file` has the ABI and sealed-handle behavior, but still
  needs VFS byte snapshot population.
- Dataset and queue handles are fixed table indexes; generation/capability
  tokens should be made externally visible before untrusted cross-process
  handle passing.
- Queue send/receive is bounded and deterministic, but does not yet integrate
  scheduler wakeups for blocked readers/writers.
- POSIX remains a wrapper surface. New driver, service, and Simple application
  logic should call SOSIX modules directly.
