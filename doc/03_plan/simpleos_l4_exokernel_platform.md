# Plan: SimpleOS L4/Exokernel Platform for Simple Language

**Date:** 2026-04-04
**Status:** In Progress (Phase 0-3 complete, Phase 4 in progress, Phase 5 pending)
**Research:** [local/simpleos_l4_exokernel_platform.md](../01_research/local/simpleos_l4_exokernel_platform.md)

## Objective

Evolve SimpleOS from demo kernel into L4-style microkernel + exokernel-style device model. Add POSIX compatibility layer with async-by-default interfaces. Make Simple language the primary supported runtime.

## Architecture

Kernel objects: Task, Thread, VmSpace, Page, Endpoint, Notification, Irq, DeviceMem, DmaWindow, IommuDomain, PciFunction

Capsule graph: init → {pager, log, pcimgr} → {nvme, net, gpu} → {fs, netstack, display} → apps

## Phases

### Phase 0: Codegen Fixes — COMPLETE (2026-04-04)
- 0A: Fix global variable reads — **DONE**
  - Root cause: HIR `module_pass.rs` missed `Pattern::Typed` → type resolved as ANY → string concat instead of iadd
  - Fix: `extract_pattern_type()` helper in `module_pass.rs`
  - Regression test: `test/unit/compiler/global_var_type_spec.spl` (module-level vars)
  - Verified: `pure_gui.spl` renders via `fb_addr` global (not hardcoded)
- 0B: Fix integer equality — **DONE**
  - Added `rt_native_eq`/`rt_native_neq` to `baremetal_stubs.c`
  - Handles both raw i64 identity AND heap string content comparison
  - Verified: `== 0` in `sputc()` polling loop works, serial output from Pure Simple
- 0C: Complete raw-ABI stubs — **DONE**
  - 60 real implementations replacing S-macro stubs (map, array, string, arithmetic, type introspection, debug)
  - `auto_stubs.c` (6310 lines of weak return-0 stubs) deleted
  - All port I/O and MMIO functions use raw i64 ABI (not tagged RuntimeValues)

### Phase 1: Kernel Refactoring — COMPLETE (2026-04-04)
- 1A: DTB/PCI discovery — **DONE**
  - `src/os/kernel/boot/dtb_parser.spl` (561 lines): FDT header parser, structure walker, node classification
  - Extracts UART, PLIC, CLINT, RAM from QEMU virt DTB
  - `riscv64/boot.spl` updated: uses parsed DTB with hardcoded fallback
- 1B: L4 kernel object model — **DONE**
  - `src/os/kernel/types/thread_types.spl`: Thread, BlockTarget (primitive-only fields)
  - `src/os/kernel/types/vmspace_types.spl`: VmSpace, PageMapping, page flag constants
  - `src/os/kernel/types/endpoint_types.spl`: Endpoint, IpcHeader, WaitResult
  - `src/os/kernel/types/notification_types.spl`: Notification, NOTIFY_* bit constants
  - `src/os/kernel/types/device_mem_types.spl`: DeviceGrant, PciBar, IrqObject, DmaWindow
  - `src/os/kernel/types/bitfield.spl`: Generic bit ops + PTE/capability/PCI accessors
- 1C: Capability enforcement — **DONE**
  - `syscall.spl`: cap checks before file, memory, process, network, device syscalls
  - Returns SYSCALL_EPERM on capability violations
  - Always-allowed: Exit, Yield, Wait, GetPid, Pledge, Unveil, DebugWrite
- 1D: IPC shared-memory buffers — **DONE**
  - `src/os/kernel/ipc/message_buffer.spl`: 256-entry buffer pool, page-granular alloc
  - Inline (64 bytes) + buffer transfer (zero-copy) paths
  - Send/recv with ownership transfer
- 1E: Async notification objects — **DONE**
  - `src/os/kernel/ipc/notification.spl` (189 lines): 64-slot table, bitmask signaling
  - signal/wait/poll operations, syscalls 24-28
  - Integrates with scheduler block/unblock
- 1F: QEMU scenario system — **DONE**
  - `QemuScenario` class in `qemu_runner.spl`
  - 7 scenarios: rv64-base, rv64-dtb-pci, x64-pci-lab, x64-nvme, x64-net-user, x64-gpu-2d, x64-gui
  - `get_scenario(name)`, `build_scenario_command()`

### Phase 2: POSIX + Async I/O — COMPLETE (2026-04-04)
- `src/os/posix/errno.spl`: 40 standard POSIX error codes
- `src/os/posix/fd_table.spl`: per-process FD table (256 entries, stdin/stdout/stderr on serial)
- `src/os/posix/fd_io.spl`: posix_open (returns -ENOSYS), read/write/close/lseek/dup/dup2
- `src/os/posix/async_io.spl`: async-by-default I/O over IPC, request pool (128 slots)
  - Serial: synchronous immediate completion
  - File: returns -EIO (VFS not connected yet)
- `src/os/posix/pipe_compat.spl`: returns -ENOSYS (needs endpoint create syscall)
- `src/os/posix/signal_compat.spl`: handler table, mask, pending delivery
  - posix_kill returns -ENOSYS, signal_deliver_pending is no-op safe
- `src/os/posix/process_compat.spl`: posix_spawn/waitpid return -ENOSYS, no fork by design
- `src/os/posix/mod.spl`: posix_init() initializes all subsystems
- **All unimplemented paths return -ENOSYS or -EIO — no false success**

### Phase 3: User-Space Drivers — COMPLETE (2026-04-04)
- 3A: Kernel foundation — **DONE**
  - Memory syscalls (10-12): Mmap/Munmap/Mprotect wired to VMM+PMM with bump allocator at 0x10000000
  - Device enumeration (80-81): Wired to PciBus — lazy scan, flat cache arrays, returns real PCI devices
  - IRQ-to-notification routing: `src/os/kernel/interrupts/irq_routing.spl` + `notif_global.spl`
    - `irq_dispatch_routed()` called from `idt_dispatch` for vectors 32-79
  - DeviceGrant syscall (82): Reads PCI config, creates IRQ notification, registers IRQ route
  - MapBar syscall (83): Maps physical BAR with PTE_CACHE_DISABLE into caller's VmSpace
  - AllocDma syscall (84): Contiguous DMA buffer allocation, identity mapping for no-IOMMU
  - FreeDma syscall (85): Unmaps and frees DMA pages
  - IPC message buffers: `ipc_send_inline/buffer`, `ipc_recv_buffer` fully implemented with per-endpoint circular queues
- 3B: PCI manager capsule — **DONE**
  - `src/os/services/pcimgr/pcimgr.spl` (283 lines): Enumerates devices via syscall 80, grants via syscall 82
  - `src/os/services/pcimgr/driver_match.spl` (157 lines): NVMe/VirtIO-blk/net/gpu matching by class+vendor
- 3C: NVMe driver capsule — **DONE**
  - `src/os/drivers/nvme/nvme_types.spl` (94 lines): Command opcodes, register offsets, CC/CSTS bits
  - `src/os/drivers/nvme/nvme_queue.spl` (156 lines): Submission/completion queue management with phase-based polling
  - `src/os/drivers/nvme/nvme_driver.spl` (557 lines): Full init (reset, admin queues, Identify, I/O queues), read/write/flush
- 3D: VirtIO-net driver — **DONE**
  - `src/os/drivers/virtio/virtio_net.spl` upgraded (574 lines): PCI legacy transport, DMA-based RX/TX queues, MAC read, IRQ notification wait
  - `src/os/drivers/virtio/virtio_net_service.spl` (197 lines): IPC service "net0" with send/recv/mac/status methods
- 3E: VirtIO-GPU 2D capsule — **DONE**
  - `src/os/drivers/virtio/virtio_gpu_types.spl` (89 lines): Command types, pixel formats, struct sizes
  - `src/os/drivers/virtio/virtio_gpu.spl` (697 lines): GET_DISPLAY_INFO, CREATE_2D, ATTACH_BACKING, SET_SCANOUT, TRANSFER+FLUSH
  - Drawing primitives: put_pixel, fill_rect, clear, draw_hline/vline/rect
- 3G: Userlib wrappers — **DONE**
  - `request_device_grant`, `map_bar`, `map_bar_at`, `alloc_dma`, `free_dma` added to `src/os/userlib/device.spl`
- Network syscalls (70-77): Remain as -ENOSYS stubs (Phase 3+ — needs TCP/IP stack)

### Phase 4: Simple Runtime on SimpleOS — IN PROGRESS (2026-04-04)
- 4A: Storage stack wiring — **DONE**
  - `src/os/services/vfs/vfs_init.spl` (233 lines): NvmeBlockAdapter + vfs_boot_init() orchestrates PCI→NVMe→FAT32→VFS
  - `src/os/kernel/boot/init_services.spl` (90 lines): Boot-time service spawner
  - QEMU scenarios: x64-nvme-fat32, x64-full-stack added to qemu_runner.spl
  - Disk image tool: `scripts/make_os_disk.shs` builds FAT32 test images
  - `vmm_verify_user_write()`: PTE-level copy_to_user guard in vmm.spl
- 4B: Hello world app — **DONE** (code written, needs QEMU boot test)
  - `examples/simple_os/apps/hello_world.spl`: serial print, arithmetic, loops
  - `examples/simple_os/apps/device_test.spl`: PCI enumeration via syscall 80
  - `src/os/test/phase3_driver_test.spl`: Integration test for driver stack
- 4C: Cross-compile interpreter — PENDING (alternative: compile hello.spl to native ELF via native-build)
- 4D: End-to-end test — PENDING (`simple run hello.spl` prints via serial on QEMU)

### Phase 5: Self-Hosted Compiler (6-9 months) — PENDING
- Integrated ELF linker in Simple (no external mold/lld)
- Cranelift as static library
- Native compilation on SimpleOS

## QEMU Strategy
- Primary: RISC-V `virt` (DTB discovery) + x86_64 `q35` (PCIe lab)
- Staged: emulated → vhost-user → IOMMU → VFIO passthrough
- Debug: TCG first, `-s -S` for GDB, record/replay

## Design Principles
1. Kernel owns protection only
2. Resource-oriented device grants (BAR + IRQ + DMA)
3. Async by default, sync POSIX as sugar
4. Capability-checked everywhere
5. DTB/PCI as source of truth
6. Pure Simple OS code
7. Fail-restart over fail-crash

## Key Findings (implementation)
- **Cranelift ABI**: extern fns receive raw i64, not tagged RuntimeValues
- **Global variables**: Fixed — HIR module_pass now extracts type from Pattern::Typed
- **Comparison operators**: `== 0` compiles as `call rt_native_eq` — must be provided in stubs
- **POSIX on L4**: No fork by design — use posix_spawn. No select/poll — use notification wait_any
- **VirtIO PCI**: QEMU Q35 uses PCI legacy transport (BAR0 I/O), not MMIO transport
- **NVMe doorbells**: Use CAP.DSTRD for stride; SQ tail at 0x1000+2*qid*(4<<DSTRD)
- **DeviceGrant flow**: syscall 82 reads PCI config + allocates notification + registers IRQ route
- **DMA identity**: No IOMMU �� device_addr == host_phys_addr for AllocDma syscall 84
