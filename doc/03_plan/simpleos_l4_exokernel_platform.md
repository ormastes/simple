# Plan: SimpleOS L4/Exokernel Platform for Simple Language

**Date:** 2026-04-04
**Status:** In Progress (Phase 0-2 complete, Phase 3-5 pending)
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

### Phase 3: User-Space Drivers (4-6 weeks) — PENDING
- 3A: DeviceGrant pattern + device grant syscall
- 3B: PCI manager capsule (`src/os/services/pcimgr/`)
- 3C: NVMe driver capsule (`src/os/drivers/nvme/`)
- 3D: VirtIO-net driver capsule (seL4 sDDF model)
- 3E: VirtIO-GPU 2D capsule
- Prerequisite: Phase 1 kernel objects for BAR mapping + IRQ routing

### Phase 4: Simple Runtime on SimpleOS (3-5 weeks) — PENDING
- 4A: Cross-compile Rust interpreter for x86_64-unknown-simpleos
- 4B: Test: `simple run hello.spl` prints via serial
- Prerequisite: Phase 2 POSIX file I/O (VFS service must be connected)

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
