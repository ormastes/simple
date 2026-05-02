# Design: SimpleOS Async Exokernel Services

**Date:** 2026-04-04
**Status:** Implemented (Phase 3.5)
**Plan:** [simpleos_l4_exokernel_platform.md](../03_plan/simpleos_l4_exokernel_platform.md)

## Overview

Notification-driven async I/O throughout the SimpleOS stack, from device drivers to shell and SSH server. Every component has dual interfaces: POSIX (sync, fd-based) and Simple-native (async, Future-based).

## Architecture Pattern

Synthesized from seL4 (shared rings + notifications), Fuchsia/Zircon (multiplexed wait), Redox (scheme-based routing), MIT Exokernel (libOS pattern), and Hubris (sync IPC + notification side-channel):

```
Application
  | (async API: OsFuture<T> or POSIX sync wrappers)
  v
LibOS / User-Space Service
  | (shared ring buffer in DMA memory for data path; IPC for control path)
  v
User-Space Driver Task (owns DeviceGrant)
  | (MMIO + DMA + doorbell writes)
  v
Hardware
  | (IRQ)
  v
Kernel (only involvement: IRQ -> notification signal)
  | (notification signal via existing irq_routing.spl)
  v
Driver Task wakes -> processes completion -> signals service via notification
```

Kernel is involved **only** in the IRQ-to-notification path. All data movement is in user-space.

## Key Design Decisions

### 1. OS Async Runtime vs Library Async
The existing `src/lib/nogc_async_mut/` uses host OS primitives (epoll/kqueue). It cannot run on SimpleOS. The OS-level runtime (`src/os/async/`) uses kernel notification syscalls (24-28) for wakeup instead. OsExecutor sleeps on NotificationWait (syscall 26), not spin-polling.

### 2. WaitAny via Register Arguments
Syscall 29 passes notification IDs in registers (arg0-arg3, count in arg4) rather than via a userspace pointer. This avoids baremetal pointer dereferencing complexity and supports 1-4 notifications per wait, covering the typical driver use case.

### 3. Exokernel Network Bypass
Network syscalls 70-77 remain as kernel stubs. Applications use `socket_compat.spl` which talks directly to the netstack service via IPC (port 2). This is the correct exokernel pattern: apps communicate with user-space services, not through kernel mediation.

### 4. LibOS Pattern for TCP/IP
The netstack service owns the VirtIO-net driver in-process. Frames don't cross IPC boundaries on the data path, only on the control path (socket/bind/listen/connect from apps via IPC).

### 5. PTY via POSIX Pipes
SSH PTY emulation uses two POSIX pipes instead of kernel ptmx. Master side (SSH server) writes decrypted input to one pipe, shell reads from it. Shell writes output to the other pipe, SSH server reads and encrypts it. The Terminal class handles VT100/ANSI parsing.

## Component Map

| Component | Location | Lines | IPC Port |
|-----------|----------|-------|----------|
| OS Async Runtime | `src/os/async/` | 666 | N/A |
| Kernel WaitAny | `src/os/kernel/ipc/` | +46 | N/A |
| Async NVMe | `src/os/drivers/nvme/` | +284 | N/A |
| Async VirtIO-Net | `src/os/drivers/virtio/` | +400 | N/A |
| Async VFS + FAT32 Write | `src/os/services/vfs/`, `fat32/` | +1200 | Port 1 |
| TCP/IP Stack | `src/os/services/netstack/` | 3739 | Port 2 |
| POSIX Completion | `src/os/posix/` | +800 | N/A |
| Async Shell | `src/os/apps/shell/` | +290 | N/A |
| SSH Server | `src/os/apps/sshd/` | 2911 | TCP:22 |
| Pure Crypto | `src/os/crypto/` | 1984 | N/A |

## Notification Flow (Example: NVMe Read)

1. Application calls `posix_read(fd, buf, count)`
2. POSIX layer sends VFS_READ IPC to VFS service (port 1)
3. VFS service calls FAT32 driver's `read()` method
4. FAT32 calls NVMe's `read_sectors_notify(lba, count)`
5. NVMe submits command to SQ, rings doorbell
6. NVMe calls `wait_completion_notify(notif_id, timeout)`
7. `wait_completion_notify` does quick CQ poll, then `syscall(26, notif_id, ...)` to sleep
8. NVMe device completes command, fires IRQ
9. Kernel's `irq_dispatch_routed()` signals the notification
10. Thread wakes, polls CQ, finds completion, returns data up the stack

## TCP Connection Flow (Example: SSH Accept)

1. SSH daemon calls `posix_accept(listen_fd)` 
2. `socket_compat.spl` sends NET_ACCEPT IPC to netstack (port 2)
3. Netstack checks TCP listener's accept queue
4. If empty, blocks (waits for notification from TCP state machine)
5. VirtIO-net IRQ fires with SYN packet -> notification -> netstack wakes
6. Netstack processes: Ethernet -> IPv4 -> TCP SYN -> creates connection, sends SYN+ACK
7. Client ACK arrives -> connection moves to Established -> queued in accept queue
8. Netstack replies to NET_ACCEPT IPC with new socket fd
9. SSH daemon receives client fd, starts SSH session

## Crypto Design

All crypto is pure Simple (no SFFI), running on baremetal:
- **SHA-256**: Full FIPS 180-4 with 64 round constants, HMAC-SHA-256
- **AES-256-GCM**: Full S-box, 14-round key expansion, GF(2^128) multiplication for GHASH
- **Curve25519**: 5-limb (51-bit) field arithmetic, Montgomery ladder, Fermat inversion
- **CSPRNG**: RDRAND-seeded, ChaCha20-based stream for uniform random bytes
