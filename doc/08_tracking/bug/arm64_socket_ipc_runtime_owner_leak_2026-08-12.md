# ARM64 Socket IPC Runtime Owner Leak
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-12  
**Status:** STATIC REPAIR PRESENT — target link confirmation pending  
**Acceptance criteria:** SOSIX/QEMU ARM64 build admission

## Reproducer

The ARM64 SimpleOS entry closure imports `os.kernel.fd_io`, which imports
`os.kernel.socket_compat` solely so generic FD close can route socket FDs. The
socket module declared and called `rt_ipc_send_bytes`; only the x86_64 boot
runtime owns that symbol. ARM64 therefore failed at link time even when the
boot path never opened a socket.

## Root cause and repair

An architecture-neutral socket API directly owned a target-specific raw
runtime bridge. `os.kernel.net.socket_ipc_transport` now confines the raw
bridge to `@cfg(x86_64)`. Non-x86_64 builds return `ENOSYS` for send and the
existing empty-record failure sentinel for receive. They do not claim success
and no ARM64 stub provider was added.

Focused guard:

```text
test/01_unit/os/kernel/net/socket_ipc_transport_link_contract_spec.spl
```

## Remaining evidence

A future ARM64 build owner must confirm the target link has no undefined
`rt_ipc_send_bytes` or `rt_ipc_recv_bytes`. Per the delegated lane contract,
this repair did not rebuild the ARM64 kernel or run QEMU.

## 2026-11-05 drift and re-repair

The guard spec was executed on the aarch64 Linux host (seed
`src/compiler_rust/target/bootstrap/simple`, interpreter mode) and found the
repair had **drifted**: 1/3 passed, 2/3 failed.

- `src/os/kernel/socket_compat.spl` had re-acquired direct
  `extern fn rt_ipc_send_bytes` / `extern fn rt_ipc_recv_bytes` declarations
  and called them at five sites (`_net_ipc_request`,
  `_net_ipc_request_bytes`, `_net_close_remote`), re-opening the link leak the
  transport boundary exists to prevent.
- `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c` carried a
  fabricated ARM64 provider for both symbols in the stub table
  (`S3(rt_ipc_send_bytes) S2(rt_ipc_recv_bytes)`).

Re-repair (this lane):

- `socket_compat.spl` drops both raw extern declarations and routes all five
  call sites through the architecture-neutral
  `os.kernel.net.socket_ipc_transport.{socket_ipc_send_bytes,
  socket_ipc_recv_bytes}` wrappers (x86_64 → raw bridge, other targets →
  ENOSYS / empty-record sentinel).
- `baremetal_stubs.c` stub-table entries for both symbols removed.

Re-verification: `socket_ipc_transport_link_contract_spec.spl` 3/3 PASS on the
aarch64 host (2026-11-05). Remaining acceptance unchanged: SOSIX/QEMU ARM64
build admission (target link must show no undefined `rt_ipc_*_bytes`).
