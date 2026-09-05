# SimpleOS ARM64 EL0 server syscall and VirtIO-net gap (2026-08-14)

## Status

Claimed by `arm64_net_runtime_impl`; **partially fixed, still open** until real
VirtIO-net and QEMU evidence prove the affected paths. This record is the
source-edit ownership claim.

## Exact pre-fix reproduction

- `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:1211`
  dispatches only exit, getpid, debug output, and device/DMA calls; every other
  mounted EL0 syscall returns `-38` (`ENOSYS`).
- `src/os/kernel/abi/syscall_shim_net.spl:45` through the syscall-76 shim send
  pointer-shaped POSIX arguments to `src/os/kernel/ipc/syscall_net.spl`, whose
  `_forward_net_ipc` is an unconditional `-38`. In particular, the ABI docs say
  `a1` is a `sockaddr` pointer while the IPC helper treats it as a packed IPv4
  scalar. An ordinary mounted HTTP executable therefore cannot bind, listen,
  accept, send, or receive.
- `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c:3439`
  leaves ARM64 VirtIO-blk writes as `ENOSYS`, so the FAT32 database durability
  path cannot honestly persist a value.
- ARM64 QEMU has no boot entry that discovers a real VirtIO-net transport,
  starts the shared `NetstackService`, and binds it to IPC port 2. Existing
  loopback support is not host-visible NIC evidence.

## Owner and boundary rationale

The shared pure-Simple ABI/network/file owners are inspected and fixed first:
`src/os/kernel/abi`, `src/os/kernel/socket_compat.spl`, `src/os/services/netstack`,
and `src/os/services/vfs`. C/assembly changes are permitted only for the proven
EL0 trap/runtime or MMIO boundary in the ARM64 boot capsule. The kernel owns
mutable fd, socket, filesystem, and NIC queue state; EL0 supplies bounded copied
bytes or validated user virtual addresses and receives scalar result receipts.
No user pointer becomes an unbounded shared loan.

## Acceptance and regressions

1. Raw syscall shims 71--76 validate and marshal POSIX `sockaddr_in` and byte
   buffers into the shared socket owner rather than `_forward_net_ipc`.
2. Invalid/null/short address inputs fail with `-EFAULT`/`-EINVAL`; this is the
   adjacent pointer-boundary regression.
3. ARM64's real SVC dispatcher reaches the same syscall contract for mounted
   EL0 code, with no marker/x86 substitution.
4. A real QEMU VirtIO-net device backs host-visible TCP, and the retained
   `SimpleOsServerExecutionReceiptV1` records mode `qemu-arm64-cpu`.
5. ARM64 block writes and reboot persistence are proven against the mounted
   filesystem, or this record remains open with the exact failing gate.

## Resume commands

Use the canonical ARM64 media builder and QEMU system gate selected by the
server execution matrix. Run each unchanged criterion once and stop after at
most three distinct fix cycles. Do not accept the x86 server gate, loopback, or
serial markers as ARM64 network/database proof.

## 2026-08-14 implementation handoff

- `src/os/kernel/abi/syscall_shim_net.spl` now routes IDs 71--76 to the shared
  POSIX socket owner. `sockaddr_in` and send payloads use
  the architecture-selected `user_copy` facade. ARM64 delegates to the recorded
  TTBR0 page-table owner, verifies every crossed page as EL0-accessible (and
  writable for copyout), rejects wraparound, and translates each byte before
  access. Other architectures retain the generic VMM walker. Null, short, wrapped,
  high-half/cross-boundary, oversized, and unsupported address-output shapes
  fail before dereference.
- Address representation was checked against all three owners:
  `socket_compat.sockaddr_in`, `socket_compat._ipv4_addr_text`, and
  `userlib.net._pack_sockaddr` store IPv4 octet 0 in the low byte; POSIX port
  bytes remain network-big-endian.
- ARM64 `userlib__syscall_raw__syscall` now selects exact kernel-local
  `spl_arm64_net_*_direct` exports only after the real MMIO NIC reports ready;
  otherwise it falls back to the generic owner or fails closed with `ENOSYS`.
  Syscall 33 removes/reuses network descriptors and then routes non-owned fds
  to VFS close. Syscall 78 reaches the filesystem sync owner.
- Adjacent regressions were added to both registered syscall-shim spec mirrors.
  The admitted Stage-2 compiler could not execute them: its single diagnostic
  compile stopped on pre-existing unsupported grammar in
  `src/os/kernel/loader/process_image.spl` and other shared kernel modules.
  This is not PASS evidence and was not retried.
- The ARM boundary now owns a modern VirtIO-MMIO NIC with bounded RX/TX rings,
  feature/status negotiation, cache maintenance, interrupt acknowledgement,
  and deterministic polling wired into the shared `NetstackService`. Host C
  syntax and `git diff --check` pass for the converged source.
- The ARM C network dispatcher now fails closed unless the architecture-neutral
  `spl_shim_net_capability_check` authorizes the current scheduler task through
  the canonical `IpcManager.cap_check` owner. This gate precedes both direct
  NIC and generic fallback dispatch; unlinked capability ownership denies.
- File open/read require the canonical `FileRead` authority; write/sync require
  `FileWrite`. Close remains always allowed because it only releases a
  caller-owned descriptor. The ARM launch installs the scheduler task's exact
  capability pouch into its fresh IPC manager before enabling either gate.
- Direct network descriptors are keyed by scheduler task, deny stale cross-task
  use, and are closed/removed at EL0 teardown. Every consumed VirtIO RX entry
  is reposted even for malformed ids/lengths or undersized caller buffers, so
  the bounded receive queue conserves descriptors. ARM ring-3 device syscalls
  80--87 now fail closed rather than exposing ambient device/BAR/DMA/IRQ
  authority. RX ownership is tracked per descriptor; a malformed or duplicate
  completion with no trustworthy posted owner fails and disables the device
  instead of guessing a descriptor identity.
- Still open: storage policy currently forbids builds/QEMU, so device init,
  cross-page EL0 copy, and host-visible HTTP remain unproved live criteria.
