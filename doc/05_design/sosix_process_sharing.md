<!-- codex-design -->
# SOSIX Process Sharing Design

## APIs

`os.sosix.process` owns async process requests:

- `sosix_process_fork`
- `sosix_process_execve`
- `sosix_process_spawn`
- `sosix_process_waitpid`
- `sosix_process_getpid`
- `sosix_process_signal`
- `sosix_process_exit`
- `sosix_process_wait_request`

`os.sosix.share` owns immutable sharing:

- `sosix_dataset_create(size, flags)`
- `sosix_dataset_write(handle, offset, bytes)`
- `sosix_dataset_seal(handle)`
- `sosix_dataset_read_byte(handle, offset)`
- `sosix_queue_create(capacity, max_msg_bytes, flags)`
- `sosix_queue_send(queue, bytes, attached_dataset)`
- `sosix_queue_recv(queue)`
- `sosix_queue_poll(queue)`

The kernel exposes the same process-sharing model through syscall IDs 120-131:

- `120 dataset_create(size, flags)`
- `121 dataset_create_from_file(fd, offset, len, flags)`
- `122 dataset_write(handle, offset, ptr, len)`
- `123 dataset_seal(handle)`
- `124 dataset_map(handle, addr_hint, offset, len)`
- `125 dataset_unmap(vaddr, len)`
- `126 dataset_close(handle)`
- `127 queue_create(capacity, max_msg_bytes, flags)`
- `128 queue_send(queue, ptr, len, attached_handle)`
- `129 queue_recv(queue, out_ptr, out_len, out_attached_ptr)`
- `130 queue_poll(queue)`
- `131 queue_close(queue, mode)`

## Data Structures

Datasets use fixed-size tables for kernel-friendly behavior:

- active flag
- sealed flag
- owner
- length
- byte storage in one bounded backing array

Queues use fixed ring buffers:

- active flag
- capacity
- max message bytes
- head/tail/count
- per-slot message length
- per-slot attached dataset handle
- per-slot byte storage

## Error Policy

The first SOSIX slice returns negative POSIX-compatible errno values so POSIX
wrappers can forward results without a translation table. The public owner is
SOSIX; POSIX names are compatibility only.

`dataset_create_from_file` currently creates a sealed immutable object with the
right ABI shape. VFS-backed byte snapshot population remains a follow-up because
the current syscall dispatcher does not expose synchronous file bytes.

## Bitfield Policy

This design uses integer flags with explicit masks instead of language bitfield
syntax. If future compiler bitfield support fails while wiring capability
rights, the compiler/runtime bug should be fixed rather than encoded as a
workaround in SOSIX.
