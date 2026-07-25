# SimpleOS Implementation Status Report

**Date:** 2026-04-04
**Scope:** Full platform implementation audit
**Previous status:** [simpleos_status_2026-04-04.md](simpleos_status_2026-04-04.md)

---

## Executive Summary

SimpleOS has evolved from a demo kernel to a functional L4-style microkernel platform with:

- Protected-capability kernel with 65+ syscall handlers (x86_64 primary)
- User-space device drivers (NVMe, VirtIO-net, VirtIO-GPU)
- Async exokernel service model (notification-based, zero-copy IPC)
- TCP/IP network stack (full RFC 793 TCP state machine)
- Interactive shell with 27 built-in commands, job control, pipelines, and SSH server
- Compositor, window manager, desktop shell, and widget-based GUI library
- LLVM guest-exec lane plus Rust report-and-gate guest wrappers on the `simpleos-x86_64` bootstrap target lane
- Freestanding C library (4,922 lines across 35 files, 21 headers)
- All implementations in pure Simple language (no external runtimes)

---

## Phase Status

| Phase | Description | Status | Notes |
|-------|-------------|--------|-------|
| 0 | Codegen Baseline | COMPLETE | HIR fixes, raw ABI stubs |
| 1 | Kernel Completion | COMPLETE (x86_64) | 149 stubs in non-x86 HAL (intentional) |
| 2 | PCI/Driver Supervisor | COMPLETE | pcimgr + supervisor + registry |
| 3 | Async Driver Runtime | COMPLETE | Event loop, lifecycle, IPC helpers |
| 3.5 | Async Exokernel Services | COMPLETE | NVMe, VirtIO-net, TCP/IP, shell, SSH, crypto |
| 4 | LLVM/Clang Porting | GUEST-EXEC LANE READY | Build scripts, sysroot layout, CMake toolchain, staged guest wrapper surface |
| 5 | Rust Porting | REPORT-AND-GATE | Target spec JSON, build scripts, staged discovery surface; build operations still intentionally gated |
| 6 | Storage/Network Drivers | COMPLETE | Async NVMe + VirtIO-net with restart |
| 7 | GPU User Driver | COMPLETE | VirtIO-GPU 2D with fence/IRQ |
| 8 | GPU Acceleration | PARTIAL | Render scene abstraction done; GPU bridge created |
| 9 | GUI Library | PARTIAL | Widget tree exists; browser engine scaffold |
| 10 | Compositor/WM/Dock | PARTIAL | All components exist; launcher service added |
| 11 | Hello World App | PARTIAL | App + manifest exist; shortcut launch wired |
| 12 | Browser Sample | PARTIAL | Sample app created; end-to-end validation needed |
| 13 | POSIX/VFS Closure | MOSTLY DONE | VFS wired, shell complete, launcher added |
| 14 | SDK Packaging | PARTIAL | Sysroot exists; templates incomplete |

---

## Codebase Statistics

Measured from `src/os/` on 2026-04-04:

| Component | Files | Lines | Notes |
|-----------|-------|-------|-------|
| Kernel (`kernel/`) | 104 | 22,499 | Capability-based, 65+ syscalls |
| Libc (`libc/`) | 35 | 4,922 | 21 headers + 14 C sources |
| Services (`services/`) | 32 | 10,942 | FAT32, VFS, netstack, SSH, shell |
| Drivers (`drivers/`) | 26 | 5,586 | NVMe, VirtIO-net, VirtIO-GPU, PS/2 |
| Apps (`apps/`) | 34 | 12,987 | Desktop shell, calculator, hello_world |
| Crypto (`crypto/`) | 7 | 3,260 | SHA-256/512, AES-GCM, X25519, Ed25519 |
| Compositor (`compositor/`) | 9 | 2,523 | Double-buffered, mouse cursor, decorations |
| Desktop (`desktop/`) | 6 | 1,211 | Taskbar, launcher, app cascading |
| POSIX (`posix/`) | 10 | 2,064 | FD table, pipes, spawn, signals, select |
| Async runtime (`async/`) | 8 | 666 | OsFuture, OsExecutor, SPSC ring |
| Userlib (`userlib/`) | 11 | 1,287 | IPC helpers, service stubs |
| Shared lib (`lib/`) | 5 | 775 | Common OS types and utilities |
| Port (LLVM/Rust/GUI) | 10+ | 600+ | Cross-compilation infrastructure |
| **Total OS code** | **292** | **69,698** | `.spl` files only (excludes `.c`/`.h`) |

Including C/header files in libc, total is approximately 74,600 lines across 327 files.

---

## Architecture Highlights

### Kernel

- L4-style microkernel: no monolithic drivers, all devices in user-space
- Capability-based security: handles for memory, IPC ports, interrupts
- 65+ syscall handlers including spawn, IPC send/recv, grant, notification, memory map
- x86_64: full Multiboot2/Limine boot, COM1 serial, framebuffer fill proven in QEMU

### Networking

- Full TCP/IP stack in pure Simple: Ethernet, ARP, IPv4, ICMP, UDP, TCP
- TCP implements all 14 RFC 793 state transitions, 3-way handshake, retransmission with exponential backoff, TIME_WAIT with 2MSL, MSS segmentation
- SSH server: Curve25519-SHA256 key exchange, AES-256-GCM, Ed25519 host keys, password auth

### File System

- FAT32 with full read/write support (no LFN, no journaling)
- Async VFS layer with IPC service (port 1), 11 operations
- Block cache with LRU eviction and dirty tracking

### Cross-Compilation Infrastructure

- **LLVM/Clang:** Sysroot with headers, static archive, linker script, CMake toolchain file, and a staged guest wrapper surface that reports `lane=x86_64-simpleos status=guest-exec`.
- **Rust:** Target spec JSON (`x86_64-unknown-simpleos.json`), build scripts, 2 example programs (`hello.rs`, `ipc_sample.rs`), and staged guest discovery commands that report `status=report-and-gate` for unsupported build operations.

---

## Known Limitations

1. **Non-x86_64 architectures are stubbed** -- ARM64 and RISC-V HAL have entry points but no working drivers or GUI. RISC-V32 has no Cranelift backend at all.
2. **LLVM/Rust cross-builds need external source** -- Framework is complete but actual compilation requires checking out LLVM source or installing Rust nightly with `rust-src`.
3. **No fork() by design** -- L4 microkernel uses `posix_spawn` (syscall 13). This is intentional, not a bug.
4. **Single-threaded only** -- pthreads exist as no-op stubs. Kernel supports one thread per process.
5. **No dynamic linking** -- Static linking only. No `dlopen`/`dlsym`.
6. **FAT32 limitations** -- No long filename (LFN) support, no journaling, no fsck.
7. **No QEMU end-to-end validation** -- Individual components are implemented but a full boot-to-SSH test has not been performed.
8. **GUI untested on real framebuffer** -- Compositor, desktop shell, and widgets exist but have not been validated in QEMU with Limine framebuffer.
9. **Browser is scaffold only** -- Type definitions exist but no rendering or layout engine.
10. **TCP has no congestion control** -- Fixed window only, no slow start or AIMD.

---

## Smoke Test Hardening (This Report)

Two smoke test files were hardened to support graceful degradation:

### LLVM Smoke Tests (`src/os/port/llvm/test_smoke.spl`)

- **Phase 1 (sysroot-only):** Validates 6 required sysroot files (3 headers, 1 static lib, 1 CRT object, 1 linker script), checks header non-emptiness, and inspects libc symbols via `nm`
- **Phase 2 (compilation):** Original clang/lld tests, only run when tools are available
- **Graceful skip:** Reports "LLVM not built -- sysroot-only validation" when clang is missing

### Rust Validate Subcommand (`src/os/port/rust/build.spl`)

- Checks target spec JSON for required fields (`arch`, `data-layout`, `llvm-target`)
- Verifies `libsimpleos_c.a` exists for linking
- Confirms example source files are present
- Reports "Rust nightly not installed -- static validation only" when `rustc +nightly` is unavailable

---

## Next Steps (Priority Order)

1. **QEMU end-to-end test:** Boot x86_64, mount FAT32 on NVMe, establish TCP connection, SSH from host
2. **Timer interrupt:** PIT or APIC timer for clock updates, TCP retransmission timers
3. **DHCP + DNS:** Auto-configure IP, resolve hostnames
4. **LLVM cross-build:** Check out LLVM source, run full sysroot build, compile a C program for SimpleOS
5. **Rust cross-build:** Install nightly, run `cargo build -Z build-std=core,alloc --target x86_64-unknown-simpleos.json`
6. **GUI validation:** QEMU test with Limine framebuffer, compositor + desktop shell
7. **ARM64/RISC-V HAL:** Implement device drivers and boot paths for non-x86 architectures
8. **Multi-threaded support:** Kernel thread creation syscall, real pthreads implementation
