# Owned-Copy IPC Syscall v1 Specification

Executable source: `test/01_unit/os/kernel/ipc/ipc_owned_syscall_v1_spec.spl`

The unit contract proves that additive syscall IDs 132 and 133 do not alter
legacy IPC IDs 20 and 21. Send copies at most 4096 bytes from a checked user
mapping, obtains the caller identity from scheduler state, and accepts a
claimed reply/source endpoint only when `IpcManager.send_owned` verifies that
the current task owns it.

Receive is nonblocking in v1. It preflights the complete 32-byte little-endian
header plus payload, returns `EAGAIN` for an empty queue, `EMSGSIZE` without
consuming for insufficient capacity, and `EFAULT` without consuming for an
invalid destination. Finite timeout policies return `ENOSYS`: the current trap
continuation API cannot safely retain the destination and resume copyout after
blocking, so the ABI fails closed rather than pretending a blocked receive has
completed.

The output wire record is:

| Offset | Field |
|---:|---|
| 0 | source endpoint, `u64` little-endian |
| 8 | destination endpoint, `u64` little-endian |
| 16 | method/API, `u32` little-endian |
| 20 | flags, `u32` little-endian |
| 24 | payload length, `u32` little-endian |
| 28 | capability count (zero in v1), `u32` little-endian |
| 32 | owned payload bytes |
