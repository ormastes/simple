<!-- codex-design -->
# SOSIX Process Sharing Agent Tasks

> Status: COMPLETE — All files implemented: process.spl, share.spl, io.spl, mod.spl, socket_share.spl, dylib_share.spl, fd_ownership.spl, dataset_vfs.spl, queue_notify.spl, io_compat.spl, io_rw.spl, io_state.spl, process_compat.spl all present in src/os/sosix/ (2026-05-20 audit)

## Implemented Slice

- Add `src/os/sosix/process.spl` as the async process owner.
- Add `src/os/sosix/share.spl` for immutable datasets and bounded MPMC queues.
- Add `src/os/sosix/io.spl` as the async I/O owner.
- Add `src/os/sosix/mod.spl` initialization.
- Refactor `src/os/posix/process_async.spl` into compatibility forwarding.
- Refactor `src/os/posix/async_io.spl` into compatibility forwarding.
- Add kernel `shared_dataset` and `process_queue` managers.
- Wire syscall IDs 120-131 to dataset/queue handlers.
- Add focused SOSIX unit tests.

## Follow-Up Slice

### Done
- `socket_share.spl` — SCM_RIGHTS-style FD-pass handle table (netstack owns socket impl).
- `dylib_share.spl` — cross-process dylib grant/revoke capability table.
- `fd_ownership.spl` — FD ownership transfer (HELD → TRANSFERRING → TRANSFERRED state machine).
- `mod.spl` wires all three `*_init()` calls at SOSIX boot.

### Remaining TODO
- Populate `dataset_create_from_file` from VFS bytes.
- Add scheduler-aware queue blocking and notification wakeups.
