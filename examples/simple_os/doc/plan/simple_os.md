# Simple OS - Implementation Plan

**Version:** 0.1.0
**Last Updated:** 2026-03-15

---

## Overview

Simple OS development is organized into 4 milestones, progressing from a minimal bootable kernel to a full-featured microkernel with virtual process support. Each milestone produces a testable, demonstrable system.

---

## Milestone 1: Minimal Bootable Kernel (Target: 8 weeks)

**Goal:** Boot on QEMU x86, print to serial, handle interrupts, run a single user-space task.

### Deliverables

| # | Deliverable | Description | Test |
|---|-------------|-------------|------|
| 1.1 | x86 boot stub | Multiboot header, GDT, IDT, stack setup | Boot smoke test (serial output "[BOOT OK]") |
| 1.2 | Serial driver | UART 16550 output for debug printing | `debug_putchar` outputs to QEMU serial |
| 1.3 | Frame allocator | Bitmap-based physical page allocator | Unit test: alloc, free, reuse, exhaustion |
| 1.4 | Page table setup | Identity-mapped kernel + user-space mapping | Boot with paging enabled |
| 1.5 | Interrupt handling | IDT, PIC/APIC init, timer IRQ | Timer tick count increments |
| 1.6 | Capability table | CapTable, CapSlot, CapRights, basic operations | Unit test: insert, lookup, mint, revoke |
| 1.7 | TCB + scheduler | Thread control block, single-priority scheduling | One user-space task runs |
| 1.8 | System call interface | `int 0x80` handler, dispatch table | User task calls `debug_putchar` via syscall |
| 1.9 | Initial task | Minimal init process loaded at boot | Init prints "Hello from user space" |

### Key Decisions
- x86 32-bit only (simplest to get running on QEMU)
- No IPC yet (single task)
- No MCS scheduling yet (fixed-priority only)
- Kernel and user share same binary (linked together, separated by page tables)

### Exit Criteria
- `qemu-system-i386 -kernel build/simple_os.elf` boots and prints "[BOOT OK]"
- User-space task runs and outputs via serial
- Frame allocator unit tests pass in hosted mode
- Capability table unit tests pass in hosted mode

---

## Milestone 2: IPC + Multi-Task (Target: 8 weeks)

**Goal:** Synchronous IPC between two user-space tasks, notifications, fault handling, MCS scheduling.

### Deliverables

| # | Deliverable | Description | Test |
|---|-------------|-------------|------|
| 2.1 | Endpoint object | Synchronous IPC rendezvous point | Unit test: endpoint state transitions |
| 2.2 | IPC buffer | 4KB per-thread message buffer | Unit test: write/read MRs |
| 2.3 | Send/Recv/Call/ReplyRecv | Core IPC operations | Integration: two tasks exchange messages |
| 2.4 | Fast-path IPC | Register-only transfer for short messages | Benchmark: <1000 cycles round-trip |
| 2.5 | Notification object | Async signaling with bitmap word | Unit test: signal/wait/poll |
| 2.6 | Fault delivery | Page faults delivered as IPC to handler | Integration: page fault handled by pager |
| 2.7 | CSpace (multi-level) | Radix tree of CNodes with guard | Unit test: multi-level lookup |
| 2.8 | Untyped retype | Create typed objects from Untyped memory | Unit test: retype, revoke reclaims memory |
| 2.9 | MCS scheduler | Budget/period temporal isolation | Unit test: budget exhaustion deschedules |
| 2.10 | Priority donation | SchedContext lending during IPC | Integration: no priority inversion |
| 2.11 | Multi-task support | Create and run multiple user-space tasks | Integration: 4 tasks run concurrently |

### Key Decisions
- Implement slow-path IPC first, then optimize fast path
- MDB implemented as doubly-linked list
- Timer tick at 1ms for budget tracking
- IPC timeout not implemented yet (infinite wait only)

### Exit Criteria
- Two user tasks exchange IPC messages (verified by serial output "[IPC_TEST_PASS]")
- Notification signal/wait works (verified by serial output)
- Page fault handling works (user task accesses unmapped page, pager maps it)
- MCS budget enforcement works (high-priority task with small budget yields to lower priority)
- All unit tests pass in hosted mode

---

## Milestone 3: Virtual Processes + Multi-Arch (Target: 12 weeks)

**Goal:** Virtual process support (Simple-native interpreter), ARM and RISC-V ports.

### Deliverables

| # | Deliverable | Description | Test |
|---|-------------|-------------|------|
| 3.1 | VP kernel object | VirtualProcess type in capability model | Unit test: VP create/destroy |
| 3.2 | Simple interpreter sandbox | Restricted Simple bytecode interpreter | Unit test: VP runs, memory confined |
| 3.3 | VP IPC | VPs use same IPC as physical processes | Integration: VP sends IPC to physical process |
| 3.4 | VP scheduling | VPs scheduled via MCS SchedContext | Unit test: VP budget enforced |
| 3.5 | ARM port (boot) | ARM Cortex-A15 boot on QEMU virt | Boot smoke test on QEMU ARM |
| 3.6 | ARM port (full) | Interrupts, MMU, context switch on ARM | IPC test passes on ARM |
| 3.7 | RISC-V port (boot) | RV32 boot on QEMU virt | Boot smoke test on QEMU RISC-V |
| 3.8 | RISC-V port (full) | Interrupts, Sv32 MMU, context switch | IPC test passes on RISC-V |
| 3.9 | Architecture HAL | Clean trait-based abstraction | All tests pass on all 3 architectures |
| 3.10 | IRQ delivery | Hardware IRQs to user-space via Notification | Serial IRQ handled by user-space driver |

### Key Decisions
- Simple-native interpreter first (lowest implementation effort)
- Wasm and SFI deferred to Milestone 4
- ARM target: QEMU `virt` machine with Cortex-A15
- RISC-V target: QEMU `virt` machine with RV32IMA

### Exit Criteria
- VP runs Simple bytecode in sandbox, communicates via IPC
- Boot smoke test passes on x86, ARM, and RISC-V QEMU targets
- IPC two-task test passes on all three architectures
- VP cannot access memory outside its designated region

---

## Milestone 4: Hardening + Performance (Target: 12 weeks)

**Goal:** Wasm VP support, SFI VP support, IPC timeouts, SMP preparation, performance optimization.

### Deliverables

| # | Deliverable | Description | Test |
|---|-------------|-------------|------|
| 4.1 | Wasm VP runtime | Embedded Wasm interpreter for VP execution | Integration: Wasm VP runs and communicates |
| 4.2 | SFI compiler pass | SFI instrumentation in Simple compiler | Integration: SFI VP runs with address masking |
| 4.3 | IPC timeouts | Bounded-time IPC operations | Unit test: send with timeout returns error |
| 4.4 | IOPort caps (x86) | I/O port access via capabilities | Integration: user-space serial driver |
| 4.5 | User-space drivers | Framework for capability-mediated drivers | Integration: keyboard driver in user space |
| 4.6 | Performance tuning | Fast-path optimization, cache alignment | Benchmark: IPC < 800 cycles round-trip |
| 4.7 | Stress testing | Concurrent tasks, large CSpaces, memory pressure | Soak test: 64 tasks running for 1 hour |
| 4.8 | Documentation | API reference, architecture guide, tutorial | Review: docs cover all syscalls |
| 4.9 | SMP groundwork | Per-CPU data structures, spinlocks, IPI | Design doc: SMP architecture |

### Key Decisions
- Wasm interpreter (~60KB code) embedded in kernel supervisor process
- SFI verification runs at VP load time (not at compile time)
- SMP is design-only in M4 -- implementation deferred to M5
- Performance benchmarks run on bare-metal x86 (not just QEMU)

### Exit Criteria
- Wasm VP and SFI VP both functional and communicating via IPC
- IPC timeout works correctly (sender/receiver unblocked on timeout)
- User-space serial driver works via IOPort capabilities
- IPC round-trip benchmark < 1000 cycles on x86
- 64 concurrent tasks stable for 1 hour on QEMU

---

## Risk Register

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Simple compiler bugs block kernel development | High | Medium | Test compiler with kernel patterns early; report bugs upstream |
| Performance too slow for real-time guarantees | Medium | Low | Profile early; use SFFI for critical paths |
| ARM/RISC-V porting more complex than expected | Medium | Medium | Start with QEMU virt (simplest platform); share HAL design |
| Wasm runtime too large for embedded targets | Low | Medium | Use interpreter-only (no JIT); target ~60KB code size |
| MCS scheduling introduces subtle timing bugs | Medium | Medium | Extensive unit testing; formal specification of scheduler invariants |
| CSpace complexity leads to capability leaks | High | Low | Implement revocation tests early; test MDB invariants |

---

## Resource Estimates

| Milestone | Estimated LOC (Simple) | Estimated LOC (Tests) | Duration |
|-----------|----------------------|----------------------|----------|
| M1: Minimal Boot | ~2,000 | ~500 | 8 weeks |
| M2: IPC + Multi-Task | ~4,000 | ~1,500 | 8 weeks |
| M3: VP + Multi-Arch | ~5,000 | ~2,000 | 12 weeks |
| M4: Hardening | ~4,000 | ~2,000 | 12 weeks |
| **Total** | **~15,000** | **~6,000** | **40 weeks** |

---

## Dependencies

| Dependency | Required By | Status |
|------------|-------------|--------|
| Simple compiler baremetal target | M1 | Available (baremetal-x86 preset) |
| Simple nogc_async_mut_noalloc stdlib | M1 | Available |
| SFFI for inline assembly | M1 | Available |
| Simple-to-Wasm compiler backend | M4 | Not started |
| QEMU x86/ARM/RISC-V | M1/M3 | Available (system packages) |
