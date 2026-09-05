# ARM64 Socket IPC Runtime Owner Leak

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
