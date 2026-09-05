# SOSIX VFS IPC Receive ABI Mismatch

**Status:** open blocker for true asynchronous VFS completion  
**Date:** 2026-08-11

## Contradiction

- `src/os/kernel/ipc/syscall_ipc.spl:57` defines syscall 21 argument 1 as a
  timeout and returns only success/EAGAIN state.
- `src/os/kernel/abi/syscall_shim_ipc.spl:40` documents argument 1 as a user
  message-buffer pointer and argument 2 as capacity.
- `src/os/services/vfs/vfs_service.spl:145` treats the syscall return as an IPC
  message address.
- `src/os/sosix/io_rw.spl` passes a reply-buffer pointer/capacity and expects
  the kernel to fill that buffer.

These conventions cannot all be correct. A SOSIX completion worker cannot
safely parse/correlate replies until syscall 21 has one executable ABI.

The 2026-08-11 full call-chain audit also proves the send side is broken:

- syscall 20 constructs only `IpcMessage` metadata and never reads `arg3` or
  copies the declared payload;
- `IpcManager.send` deliberately queues `LegacyMetadata` with `payload: []`,
  while the separate owned-copy `send_owned`/`recv_owned` path is not wired to
  a syscall;
- VFS READ declares `handle:u64 + size:u64`, but SOSIX sends
  `method:u32 + handle:u64 + offset:u64 + count:u64`;
- VFS READ replies with `status:i32 + raw bytes`, while SOSIX decodes
  `status:i32 + transferred:u64 + raw bytes`;
- the VFS reply helper passes `(dst, src_port, data_ptr, data_len, 0)` to a
  syscall interpreted as `(dst, method, flags, payload_ptr, payload_len)`;
- there is no authenticated reply endpoint, request token, source filter, or
  guarantee that hard-coded port 1 is the allocated VFS service port; and
- the x86 bare-metal C shim implements a third, single-global-reply ABI and is
  not evidence for the kernel/VFS path.

Consequently, current QEMU filesystem boot/list/program evidence does not prove
SOSIX VFS IPC: production filesystem syscalls use separate direct paths and the
VFS service is not spawned on those acceptance lanes.

## Required resolution

Wire one owned-copy IPC surface, preferably new versioned syscalls rather than
overloading inconsistent 20/21. Freeze an authenticated source and reply
endpoint plus `(operation slot, generation, request token)` correlation. Use
explicit `READ_AT`/`WRITE_AT` descriptors backed by registered buffers. Update
the kernel dispatcher and shim together, add byte-level and real round-trip
tests, then migrate VFS service and SOSIX callers in the same integration
change. A dedicated nonblocking completion pump owns each reply endpoint.

## Acceptance to unblock

1. One syscall-21 signature is documented and implemented in all modes.
2. A nonblocking receive distinguishes EAGAIN from a valid zero-length message.
3. Payload and correlation ID round-trip through a real IPC test.
4. VFS replies identify the exact `SosixOperationId`.
5. `sosix_async_read/write` submit without receiving; a completion worker
   performs receive and terminal transition.
