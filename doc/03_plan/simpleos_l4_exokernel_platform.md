# Plan: SimpleOS L4/Exokernel Platform for Simple Language

**Date:** 2026-04-04
**Status:** Approved
**Research:** [local/simpleos_l4_exokernel_platform.md](../01_research/local/simpleos_l4_exokernel_platform.md)

## Objective

Evolve SimpleOS from demo kernel into L4-style microkernel + exokernel-style device model. Add POSIX compatibility layer with async-by-default interfaces. Make Simple language the primary supported runtime.

## Architecture

Kernel objects: Task, Thread, VmSpace, Page, Endpoint, Notification, Irq, DeviceMem, DmaWindow, IommuDomain, PciFunction

Capsule graph: init → {pager, log, pcimgr} → {nvme, net, gpu} → {fs, netstack, display} → apps

## Phases

### Phase 0: Codegen Fixes (1-2 weeks)
- 0A: Fix global variable reads (common_backend.rs)
- 0B: Fix integer equality (core.rs → native icmp for baremetal)
- 0C: Complete raw-ABI stubs (rt_map_*, rt_native_eq)

### Phase 1: Kernel Refactoring (4-6 weeks)
- 1A: DTB/PCI discovery (replace hardcoded board constants)
- 1B: L4 kernel object model (Thread, VmSpace, Endpoint, Notification)
- 1C: Capability enforcement at all syscall boundaries
- 1D: IPC shared-memory payload buffers
- 1E: Async notification objects
- 1F: QEMU scenario system

### Phase 2: POSIX + Async I/O (3-4 weeks)
- 2A: Per-process file descriptor table
- 2B: POSIX file I/O wrappers (sync over async IPC)
- 2C: Async I/O layer (HostRuntime-based)
- 2D: Process compatibility (posix_spawn, no fork)
- 2E: Pipes and signals
- 2F: errno codes

### Phase 3: User-Space Drivers (4-6 weeks)
- 3A: DeviceGrant pattern + device grant syscall
- 3B: PCI manager capsule
- 3C: NVMe driver capsule
- 3D: VirtIO-net driver capsule
- 3E: VirtIO-GPU 2D capsule

### Phase 4: Simple Runtime on SimpleOS (3-5 weeks)
- 4A: Cross-compile interpreter for x86_64-unknown-simpleos
- 4B: Test: `simple run hello.spl` prints via serial

### Phase 5: Self-Hosted Compiler (6-9 months)
- Integrated ELF linker in Simple
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
