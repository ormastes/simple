# SimpleOS Status Report -- 2026-04-04

**Previous:** [simpleos_status_2026-04-02.md](simpleos_status_2026-04-02.md)
**Phase 3.5 (Async Exokernel Services):** COMPLETE
**Design:** [simpleos_async_exokernel_services.md](../05_design/simpleos_async_exokernel_services.md)

---

## 1. Boot Status per Architecture

| Architecture | Entry Point | Boot Method | Serial | Framebuffer | GUI Entry | Status |
|-------------|-------------|-------------|--------|-------------|-----------|--------|
| **x86_64** | `arch/x86_64/entry.spl` | Multiboot2/Limine | COM1 0x3F8 | Limine LFB | `gui_entry.spl` | Working (serial + FB fill proven) |
| **arm64** | `arch/arm64/entry.spl` | Device tree | UART | -- | -- | crt0.S + boot_main added |
| **riscv64** | `arch/riscv64/entry.spl` | SBI/OpenSBI | UART | -- | -- | Boots, enters boot_main |
| **riscv32** | `arch/riscv32/entry.spl` | SBI | UART | -- | -- | Stub only (no Cranelift backend) |

**x86_64** is the only architecture with a GUI entry point. Others have serial entry points.

---

## 2. GUI Compositor Status

**Status: Implemented, untested on hardware (unchanged)**

- Compositor: window management, double-buffered, mouse cursor, decorations, input routing, drag, keyboard shortcuts
- Desktop Shell: taskbar, app launcher, built-in apps (Calculator, Clock, Terminal), window cascading
- **Needs:** Real QEMU/Limine test, timer interrupt, wallpaper loading, window restore

---

## 3. File System Status

### FAT32 (`src/os/services/fat32/`)

**Status: Read/Write implementation complete (Phase 3.5)**

| Operation | Status | Notes |
|-----------|--------|-------|
| `mount` | Working | Parses BPB, computes data region |
| `open` | Working | Path resolution + create-on-open via write context |
| `read` | Working | Follows FAT chain, cluster-level reads |
| `readdir` | Working | Lists 8.3 directory entries |
| `stat` | Working | Returns FsNode with size/permissions |
| `seek` | Working | Computes offset within cluster chain |
| **`write`** | **Working** | **Cluster allocation, FAT chain extension, directory entry update** |
| **`mkdir`** | **Working** | **Allocates cluster, creates . and .. entries** |
| **`rmdir`** | **Working** | **Checks empty, frees clusters, marks entry deleted** |
| **`unlink`** | **Working** | **Frees cluster chain, marks 0xE5** |
| **`rename`** | **Working** | **Creates new entry, marks old deleted (no data copy)** |
| `close` | Working | |

**New in Phase 3.5:**
- `fat32_write.spl`: cluster allocation (`allocate_cluster`, `extend_chain`), FAT table read/write, directory entry creation (`create_file`, `create_directory`), file data write, delete/rename
- No LFN support (8.3 only), no journaling

### VFS (`src/os/services/vfs/`)

**Status: Async routing + IPC service complete (Phase 3.5)**

- `VfsManager`: sync + async routing across mounted filesystems
- `AsyncFilesystem` trait: all operations return `OsFuture<Result<T, E>>`
- `VfsService` (IPC port 1): full IPC dispatch for 11 methods (open, read, write, close, stat, readdir, mkdir, unlink, rename, seek, mount_list)
- `BlockCache`: LRU block cache with dirty tracking, write-back, configurable capacity
- `vfs_init.spl` (Phase 4A): NvmeBlockAdapter + vfs_boot_init() for PCI→NVMe→FAT32→VFS boot chain

### What's Remaining
1. LFN support (long filename entries)
2. QEMU disk image boot test (FAT32 partition on NVMe/VirtIO-blk)
3. Journaling / fsck for crash recovery

---

## 4. Networking Status

### VirtIO-Net Driver (`src/os/drivers/virtio/`)

**Status: Sync + Async frame I/O complete (Phase 3.5)**

| Operation | Status | Notes |
|-----------|--------|-------|
| `init` | Working | VirtIO device init, MAC read |
| `send_frame` | Working | Sync: VirtIO header + raw Ethernet via TX queue |
| `recv_frame` | Working | Sync: blocking wait on IRQ notification |
| **`send_frame_async`** | **Working** | **Non-blocking TX via VirtioNetSendFuture** |
| **`recv_frame_async`** | **Working** | **Non-blocking RX via VirtioNetRecvFuture** |
| **`recv_frame_poll`** | **Working** | **Non-blocking poll without syscall 26** |
| `link_up` | Working | Reads link status register |
| `mac_address` | Working | Returns MAC as [u8] |

**New traits:** `NetworkDevice` (sync), `AsyncNetworkDevice` (Future-based)

### TCP/IP Stack (`src/os/services/netstack/`)

**Status: COMPLETE (Phase 3.5) — 10 files, 3,739 lines**

| Layer | File | Status |
|-------|------|--------|
| Ethernet | `ethernet.spl` | Frame parse/build, EthAddress, padding |
| ARP | `arp.spl` | ARP table with aging, request/reply, LRU cache |
| IPv4 | `ipv4.spl` | Parse/build, routing table (longest-prefix), header checksum |
| ICMP | `icmp.spl` | Echo request/reply, destination unreachable |
| UDP | `udp.spl` | Datagram send/recv, port binding table, queued receive |
| TCP | `tcp.spl` + `tcp_connection.spl` | **Full RFC 793 state machine** — all 14 transitions, 3-way handshake, data transfer with flow control, 4-way FIN, retransmission with exponential backoff, TIME_WAIT with 2MSL, MSS segmentation |
| Socket | `socket.spl` | POSIX-like API: create/bind/listen/connect/accept/send/recv/close |
| Service | `netstack_service.spl` | IPC port 2, owns VirtIO-net in-process (libOS pattern), event loop: frame poll + IPC dispatch + TCP timers + ARP aging |

### What's Remaining
1. DHCP client integration (tool exists at `src/os/tools/net/dhcp_client.spl`, needs wiring)
2. DNS resolver integration
3. QEMU networking test (TAP bridge or user-mode with port forwarding)
4. TCP congestion control (currently fixed window only)

---

## 5. SSH Server Status

**Status: COMPLETE (Phase 3.5) — 10 files, 2,911 lines**

| Component | File | Status |
|-----------|------|--------|
| Packet protocol | `ssh_packet.spl` | SSH binary packet (RFC 4253 sec 6), big-endian helpers |
| Transport | `ssh_transport.spl` | Version exchange, KEXINIT, algorithm negotiation |
| Key exchange | `ssh_kex.spl` | Curve25519-SHA256 (RFC 8731), session key derivation (RFC 4253 sec 7.2) |
| Encryption | `ssh_cipher.spl` | AES-256-GCM (RFC 5647), bidirectional nonce = IV XOR seq |
| Host key signing | Ed25519 (RFC 8032) | Proper `ssh-ed25519` — self-test with RFC 8032 vectors at startup |
| Authentication | `ssh_auth.spl` | Password auth with SHA-256 hashed storage, constant-time comparison |
| Channels | `ssh_channel.spl` | Channel multiplexing (RFC 4254), sliding window flow control |
| PTY | `ssh_pty.spl` | Pseudo-terminal via POSIX pipe pairs (master/slave) |
| Session | `ssh_session.spl` | Full 5-phase state machine: version → kex → service → auth → interactive |
| Daemon | `sshd.spl` | TCP listen/accept, Ed25519 host key, session limit, self-test gate |

**Security notes:**
- Ed25519 self-test (RFC 8032 test vectors) runs before key generation — daemon refuses to start if crypto fails
- Public key auth **disabled** — no Ed25519 userauth signature verification implemented yet (password only)
- Host key signing uses proper Ed25519 (not HMAC or custom scheme)

---

## 6. Async Shell Status

**Status: COMPLETE (Phase 3.5) — 1,034 lines total**

| Feature | Status |
|---------|--------|
| **27 built-in commands** | Working (cd, ls, pwd, echo, cat, mkdir, rm, cp, mv, grep, find, ps, kill, mount, env, export, history, hostname, uptime, dmesg, clear, help, exit, jobs, fg, bg, readf) |
| **Job control** | Working — `cmd &` (background), `jobs` (list), `fg N` (foreground), `bg N` (resume) |
| **Pipelines** | Working — `cmd1 \| cmd2 \| cmd3` via POSIX pipe plumbing |
| **File redirection** | Working — `>`, `>>`, `<`, `2>`, `2>>` with FD save/restore |
| **Background execution** | Working — tracks PIDs, reports done jobs after each command |
| **Bidirectional file I/O** | Working — `readf FILE` (POSIX sync), `readf --async FILE` (VFS Future) |
| **Environment variables** | Working — `$VAR` expansion, `export` |
| **Command history** | Working — index navigation |

---

## 7. Crypto Status

**Status: COMPLETE (Phase 3.5) — 3,151 lines (7 files)**

| Algorithm | File | Standard | Status |
|-----------|------|----------|--------|
| SHA-256 | `sha256.spl` | FIPS 180-4 | Working + HMAC-SHA-256 (RFC 2104) |
| SHA-512 | `sha512.spl` | FIPS 180-4 | Working (needed by Ed25519) |
| AES-256-GCM | `aes_gcm.spl` | NIST SP 800-38D | Working — full S-box, 14-round key expansion, GHASH |
| X25519 | `curve25519.spl` | RFC 7748 | Working — Montgomery ladder, scalar clamping |
| Ed25519 | `ed25519.spl` | RFC 8032 | Working — sign, verify, self-test with RFC 8032 vectors |
| ChaCha20 CSPRNG | `random.spl` | — | Working — RDRAND-seeded, ChaCha20 stream, periodic reseed |

All implementations are **pure Simple** (no SFFI/Rust FFI except `rt_rdrand` for hardware entropy).

---

## 8. OS Async Runtime Status

**Status: COMPLETE (Phase 3.5) — 666 lines (8 files)**

| Component | File | Purpose |
|-----------|------|---------|
| `OsFuture<T>` | `os_future.spl` | Trait + ReadyFuture, PendingFuture |
| `OsPoll<T>` | `os_poll.spl` | Ready/Pending enum |
| `OsWaker` | `os_waker.spl` | Signals notification via syscall 25 |
| `OsExecutor` | `os_executor.spl` | Single-threaded, sleeps on syscall 26 (NotificationWait) |
| `SpscRing` | `ring_buffer.spl` | Lock-free SPSC for DMA data paths |
| `WaitAny` | `wait_any.spl` | Multiplexed notification poll |

**Kernel enhancement:** Syscall 29 (NotificationWaitAny) — multiplex wait on up to 4 notification IDs.

---

## 9. POSIX Layer Status

**Status: Core complete (Phase 3.5)**

| Module | Status | Notes |
|--------|--------|-------|
| `errno.spl` | Working | 40 standard POSIX error codes |
| `fd_table.spl` | Working | 256-entry FD table, stdin/stdout/stderr on serial |
| `fd_io.spl` | **Working** | **posix_open/read/write/close wired to VFS IPC (port 1)** |
| `async_io.spl` | **Working** | **Async file operations via VFS IPC** |
| `pipe_compat.spl` | **Working** | **Ring-buffer pipes with notification pairs, up to 64 concurrent** |
| `process_compat.spl` | **Working** | **posix_spawn (syscall 13), waitpid (syscall 3), exit, getpid** |
| `signal_compat.spl` | **Working** | **posix_kill wired to syscall 7, signal mask management** |
| `socket_compat.spl` | **New** | **POSIX sockets over netstack IPC (port 2)** |
| `select_compat.spl` | **New** | **select/poll via notification multiplexing (syscall 29 WaitAny)** |

---

## 10. NVMe Driver Status

**Status: Sync + Async complete (Phase 3.5)**

| Operation | Status | Notes |
|-----------|--------|-------|
| `init_from_grant` | Working | Full init: reset, admin queues, Identify, I/O queues |
| `read_sectors` | Working | Sync: spin-poll CQ |
| `write_sectors` | Working | Sync: spin-poll CQ |
| `flush` | Working | Sync |
| **`read_sectors_notify`** | **Working** | **Notification-based: quick poll → syscall 26 → poll after wake** |
| **`write_sectors_notify`** | **Working** | **Same notification pattern** |
| **`flush_notify`** | **Working** | **Notification-based** |

**New traits:** `BlockDevice` (sync), `AsyncBlockDevice` (Future-based)
**New:** `NvmeAsyncCompletion` future — polls CQ, returns Ready when IRQ fires

---

## 11. Summary: End-to-End Readiness

| Subsystem | Readiness | Change | Blocking Items |
|-----------|-----------|--------|----------------|
| Boot (x86_64) | 80% | -- | Needs QEMU test with Limine ISO |
| GUI/Compositor | 70% | -- | Needs timer interrupt, QEMU framebuffer test |
| Keyboard/Mouse | 90% | -- | Needs real PS/2 hardware validation |
| Desktop Shell | 60% | -- | Needs clock timer, window restore from taskbar |
| **FAT32 FS** | **80%** | **+40%** | ~~No write support~~ Write complete; needs LFN, journaling |
| **VFS** | **85%** | **+35%** | ~~Needs FAT32 wired in~~ Async trait + IPC service done; needs QEMU test |
| **VirtIO Net** | **85%** | **+55%** | ~~No TCP/IP~~ Full TCP/IP stack; needs QEMU TAP test |
| **TCP/IP Stack** | **90%** | **NEW** | Needs DHCP, DNS, congestion control, QEMU test |
| **SSH Server** | **90%** | **NEW** | Needs QEMU E2E test, publickey auth |
| **Shell** | **95%** | **+30%** | Job control + pipes + redirection done; needs script execution |
| **Crypto** | **95%** | **NEW** | Ed25519 self-tested; needs external audit |
| **POSIX Layer** | **85%** | **+35%** | Core done; needs pty, mmap improvements |
| **Async Runtime** | **90%** | **NEW** | OsExecutor + WaitAny done; needs multi-core |
| Browser | 10% | -- | Types only, all runtime components missing |

### Recommended Next Steps (priority order)
1. **QEMU E2E test**: boot x86_64, mount FAT32 on NVMe, establish TCP connection, SSH from host
2. **Timer interrupt**: PIT or APIC timer for clock updates, TCP retransmission timers
3. **DHCP + DNS**: auto-configure IP address, resolve hostnames
4. **Phase 4**: cross-compile Simple interpreter for SimpleOS
5. **GUI**: compositor QEMU test with Limine (Workstream A)
6. **Browser**: HTML parser as first browser milestone
