<!-- codex-design -->
# SOSIX Process Sharing Agent Tasks

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

- Move socket, dylib, and remaining FD backend ownership into SOSIX.
- Populate `dataset_create_from_file` from VFS bytes.
- Add scheduler-aware queue blocking and notification wakeups.
