# Research: SimpleOS as L4/Exokernel Platform for Simple Language

**Date:** 2026-04-04
**Scope:** Local codebase analysis + architectural feasibility

## Executive Summary

SimpleOS should become an L4-style microkernel with exokernel-style device model. The kernel owns protection (address spaces, capabilities, IPC, scheduling, interrupts, memory management). User-space capsules own device management (drivers, filesystem, networking, display).

## Current State Assessment

### Kernel (src/os/kernel/) — 17,649 lines
| Component | Status | Quality |
|-----------|--------|---------|
| Heap allocator | Implemented | Free-list with coalescing |
| VMM (4-level PT) | Implemented | W^X, HHDM, huge pages |
| PMM bitmap | Implemented | 4GB max, next-fit |
| Preemptive scheduler | Implemented | 5 priorities, 256 tasks |
| IPC port messaging | Implemented | Bounded FIFO, blocking recv |
| Capability model | Framework | Enforcement incomplete |
| ELF loader | Partial | Validates only, doesn't execute |
| Syscall dispatch | Partial | 30+ defined, most stubbed |
| Signal delivery | Enum only | Not implemented |

### Devices — hardcoded, kernel-space
| Issue | Detail |
|-------|--------|
| RISC-V boot | Hardcodes UART=0x10000000, PLIC=0x0C000000 (boot.spl:33-38) |
| No DTB parsing | DTB pointer received from OpenSBI but ignored |
| PCI scan | x86 only, no RISC-V MMIO PCI |
| No IOMMU | Zero mentions in codebase |
| No DMA API | No bounce buffers, no DMA mapping |
| Drivers in user-space | Correct architecture, but no grant mechanism |

### POSIX Coverage — ~50%
| Has | Missing |
|-----|---------|
| open/read/write/close (via VFS IPC) | File descriptor table |
| spawn_binary, wait, exit | fork, exec, pipes |
| signal/kill (basic) | Signal handlers, masking |
| mmap/munmap (syscall IDs) | Implementation, brk/sbrk |
| socket/bind/listen/connect | select/poll/epoll |

### Async Infrastructure — mature
| Component | Location | Status |
|-----------|----------|--------|
| HostRuntime | nogc_async_mut/async_host | Complete |
| Future/Poll/Waker | nogc_async_mut/async/ | Complete |
| JoinSet, select, race | nogc_async_mut/async/ | Complete |
| MPSC/MPMC queues | nogc_async_mut/concurrent | Complete |
| Actor model | nogc_async_mut/ | Complete |
| Embedded runtime | nogc_async_mut/async_embedded | Complete (16 tasks) |

## Porting Feasibility

### Rust+Clang → SimpleOS: NOT FEASIBLE near-term
- Clang/LLVM: 500MB+ footprint vs 256MB RAM
- Needs CMake, Ninja, Python — no package infrastructure
- Cross-compile only; can't bootstrap on-target

### Simple Interpreter → SimpleOS: FEASIBLE (3-5 weeks)
- ~30MB footprint, minimal syscalls
- Single-threaded, no networking needed
- File I/O + serial output sufficient

### Self-Hosted Compiler → SimpleOS: LONG-TERM (6-9 months)
- Needs integrated ELF linker (no external mold/lld)
- Needs Cranelift as static library
- Needs completed compiler layers 70-90

## Key Architectural Gaps for L4/Exokernel

1. **No Thread separation** — Task = Process, can't share address spaces
2. **No Endpoint objects** — IPC uses string-named ports, not capability-based endpoints
3. **No Notification objects** — No lightweight async event mechanism
4. **No DeviceGrant** — No mechanism to grant BAR+IRQ+DMA to user-space driver
5. **IPC payload stubbed** — payload_len field exists but no buffer management
6. **Capability enforcement missing** — Capabilities stored but rarely checked
7. **DTB not parsed** — RISC-V hardcodes board constants

## Recommended Architecture

### Kernel-only objects
Task, Thread, VmSpace, Page, Endpoint, Notification, Irq, DeviceMem, DmaWindow, IommuDomain, PciFunction

### User-space capsules
init, pager, log, pcimgr, nvme, virtio-net, virtio-gpu, fs, netstack, display, apps

### Device boundary
Resource-oriented (BAR + IRQ + DMA grant), not policy-oriented ("disk", "network")

## Files Referenced
- Kernel types: `src/os/kernel/types/` (capability, ipc, memory, syscall, task types)
- IPC impl: `src/os/kernel/ipc/ipc.spl` (353 lines)
- Scheduler: `src/os/kernel/scheduler/scheduler.spl` (506 lines)
- VMM: `src/os/kernel/memory/vmm.spl` (492 lines)
- RV64 boot: `src/os/kernel/arch/riscv64/boot.spl` (194 lines, hardcoded)
- Userlib: `src/os/userlib/` (10 files)
- Async runtime: `src/lib/nogc_async_mut/` (mature, production-ready)
- Status report: `doc/09_report/simpleos_status_2026-04-02.md`
