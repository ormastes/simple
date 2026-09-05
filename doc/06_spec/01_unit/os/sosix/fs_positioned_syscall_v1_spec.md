# SOSIX FS Positioned Syscall v1

Source: `test/01_unit/os/sosix/fs_positioned_syscall_v1_spec.spl`

The dedicated positioned-I/O ABI reserves syscall 134 for registered-buffer
reads and 135 for registered-buffer writes. Its six registers contain a file
object ID, buffer registration ID, packed generation-bearing buffer identity,
resource offset, buffer offset, and length. None is a userspace address.

The current handler validates nonzero authenticated identities and overflow-safe
ranges, then returns `-ENOTSUP`. This is intentional fail-closed behavior until
the kernel-owned registry/provider can authenticate those IDs and execute the
existing SOSIX FS v1 positioned backend. It never falls back to seek emulation.

## Scenarios

- The IDs are additive after owned-copy IPC syscalls 132/133.
- A valid envelope preserves all registered identities and offsets.
- A valid request fails closed while the provider is unavailable.
- Missing identities and overflowing ranges fail as invalid input.
