# Simple OS - Implementation Plan

**Version:** 0.4.0
**Last Updated:** 2026-03-16

---

## Overview

Simple OS development is organized into phased milestones, progressing from a minimal bootable kernel to a full-featured microkernel with virtual process support. Each milestone produces a testable, demonstrable system.

---

## Current Status Summary

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 0 | Reorganize (kernel/arch/user to spl/, ref/ created) | COMPLETE |
| Phase 1 | Boot + Serial x86 (C reference boots on QEMU with [BOOT OK]) | COMPLETE |
| Phase 2 | Kernel Core x86 (all 13 kernel modules in C) | COMPLETE |
| Phase 3 | Multi-arch (6 architectures in C and Simple) | COMPLETE |
| Phase 4 | Binary Optimization (baremetal builds) | BLOCKED |

**Blocker:** Simple compiler's `build` command has a semantic error bug preventing baremetal builds. Phase 4 cannot proceed until this is resolved.

### Test Coverage

- **BDD spec files:** 12 files with 68 test cases in `test/spec/kernel/`
- **Unit test files:** 4 files in `test/unit/kernel/`
- **Integration test files:** 2 files in `test/integration/`
- **QEMU test scripts:** 8 scripts in `test/qemu/` (all 6 architectures + run_all + ipc_test)
- **Test runner status:** All 12 BDD specs load in the Simple test runner but fail at runtime with `semantic: function not found` errors (expected -- the kernel module functions are not yet linked in interpreter mode)

### Architecture Support (Phase 3)

| Architecture | C Reference | Simple Source | QEMU Boot |
|--------------|-------------|---------------|-----------|
| x86 (i386) | COMPLETE | COMPLETE | Boots with [BOOT OK] |
| x86_64 | COMPLETE | COMPLETE | Pending (multiboot fix needed) |
| ARM32 (Cortex-A15) | COMPLETE | COMPLETE | Boots with [BOOT OK] |
| AArch64 | COMPLETE | COMPLETE | Boots with [BOOT OK] |
| RISC-V32 (RV32IMA) | COMPLETE | COMPLETE | Boots with [BOOT OK] |
| RISC-V64 (RV64IMA) | COMPLETE | COMPLETE | Boots with [BOOT OK] |

---

## Phase 0: Reorganize (COMPLETE)

**Goal:** Restructure the project directory for clarity.

- Moved kernel, arch, and user source into `spl/` directory
- Created `ref/` directory for C reference implementations
- Established clean separation between Simple source and C reference

---

## Phase 1: Boot + Serial x86 (COMPLETE)

**Goal:** Boot on QEMU x86, print to serial, output "[BOOT OK]".

### Deliverables

| # | Deliverable | Description | Status |
|---|-------------|-------------|--------|
| 1.1 | x86 boot stub | Multiboot header, GDT, IDT, stack setup | COMPLETE |
| 1.2 | Serial driver | UART 16550 output for debug printing | COMPLETE |
| 1.3 | QEMU boot test | C reference boots and prints "[BOOT OK]" | COMPLETE |

### Exit Criteria (MET)
- `qemu-system-i386 -kernel build/simple_os.elf` boots and prints "[BOOT OK]"

---

## Phase 2: Kernel Core x86 (COMPLETE)

**Goal:** Implement all 13 kernel modules in C reference, with corresponding Simple source.

### Deliverables (all 13 kernel modules)

| # | Module | Description | Status |
|---|--------|-------------|--------|
| 2.1 | bitmap | Bitmap-based allocation tracking | COMPLETE |
| 2.2 | linked_list | Intrusive linked list for kernel data structures | COMPLETE |
| 2.3 | ring_buffer | Lock-free ring buffer for IPC | COMPLETE |
| 2.4 | spin_lock | Spinlock synchronization primitive | COMPLETE |
| 2.5 | frame_alloc | Physical page frame allocator | COMPLETE |
| 2.6 | frame_table | Frame metadata tracking | COMPLETE |
| 2.7 | page_table | Virtual memory page table management | COMPLETE |
| 2.8 | capability | Capability object and rights model | COMPLETE |
| 2.9 | capability_types | Capability type definitions | COMPLETE |
| 2.10 | cspace | Capability space (radix tree of CNodes) | COMPLETE |
| 2.11 | tcb | Thread control block | COMPLETE |
| 2.12 | scheduler | MCS-style scheduler with budget/period | COMPLETE |
| 2.13 | endpoint + IPC | Synchronous IPC endpoints and message passing | COMPLETE |

Additional modules: kobject, log, sched_context, ipc_buffer, notification, untyped

---

## Phase 3: Multi-Architecture (COMPLETE)

**Goal:** Port the kernel to all 6 target architectures in both C and Simple.

All 6 architectures (x86, x86_64, ARM32, AArch64, RISC-V32, RISC-V64) are implemented in both C reference and Simple source. 5 of 6 boot successfully on QEMU; x86_64 is pending a multiboot header fix.

### QEMU Test Scripts

| Script | Architecture | Status |
|--------|-------------|--------|
| `test/qemu/run_x86.shs` | x86 (i386) | Working |
| `test/qemu/run_x86_64.shs` | x86_64 | Pending fix |
| `test/qemu/run_arm32.shs` | ARM32 | Working |
| `test/qemu/run_aarch64.shs` | AArch64 | Working |
| `test/qemu/run_riscv32.shs` | RISC-V32 | Working |
| `test/qemu/run_riscv64.shs` | RISC-V64 | Working |
| `test/qemu/run_all.shs` | All architectures | Working |
| `test/qemu/run_ipc_test.shs` | IPC integration | Working |

---

## Phase 4: Binary Optimization (BLOCKED)

**Goal:** Produce optimized baremetal binaries from Simple source using the compiler's `build` command.

**Status:** BLOCKED -- the Simple compiler's `build` command encounters a semantic error bug when targeting baremetal builds. This prevents generating native binaries from the Simple `.spl` source files.

**Next steps (when unblocked):**
- Compile Simple kernel source to native baremetal binaries
- Verify boot on QEMU for all architectures from Simple-compiled binaries
- Optimize binary size and startup time
- Profile and tune IPC fast-path performance

---

## BDD Test Specs

12 BDD spec files covering all major kernel subsystems, with 68 total test cases:

| Spec File | Test Cases | Module Tested |
|-----------|------------|---------------|
| `bitmap_spec.spl` | 15 | Bitmap allocation |
| `capability_spec.spl` | 9 | Capability operations |
| `linked_list_spec.spl` | 8 | Linked list |
| `ring_buffer_spec.spl` | 8 | Ring buffer |
| `scheduler_spec.spl` | 5 | MCS scheduler |
| `untyped_spec.spl` | 5 | Untyped memory retype |
| `sched_context_spec.spl` | 4 | Scheduling context |
| `tcb_spec.spl` | 3 | Thread control block |
| `endpoint_spec.spl` | 3 | IPC endpoints |
| `ipc_spec.spl` | 3 | IPC message passing |
| `notification_spec.spl` | 3 | Async notifications |
| `cspace_spec.spl` | 2 | Capability space lookup |

All specs load successfully in the Simple test runner (discovered as spec files, BDD `describe`/`context`/`it` structure parsed correctly). They fail at runtime with `semantic: function not found` errors because the kernel module implementations are not linkable in interpreter mode -- this is expected and will resolve when Phase 4 unblocks baremetal compilation.

---

## Future Milestones (Unchanged)

### Milestone: Virtual Processes (Post Phase 4)

**Goal:** Virtual process support (Simple-native interpreter), extending multi-arch.

- VP kernel object, interpreter sandbox, VP IPC, VP scheduling
- IRQ delivery to user-space via Notification

### Milestone: Hardening + Performance (Post VP)

**Goal:** Wasm VP, SFI VP, IPC timeouts, SMP preparation, performance optimization.

- Wasm/SFI VP runtimes, IPC timeouts, IOPort caps
- User-space driver framework, stress testing, SMP groundwork

---

## Risk Register

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Simple compiler `build` bug blocks Phase 4 | **High** | **Confirmed** | Report upstream; work on test specs and C reference in parallel |
| Simple compiler bugs block kernel development | High | Medium | Test compiler with kernel patterns early; report bugs upstream |
| Performance too slow for real-time guarantees | Medium | Low | Profile early; use SFFI for critical paths |
| x86_64 multiboot fix delayed | Low | Medium | Focus on other 5 working architectures |
| Wasm runtime too large for embedded targets | Low | Medium | Use interpreter-only (no JIT); target ~60KB code size |
| MCS scheduling introduces subtle timing bugs | Medium | Medium | Extensive unit testing; formal specification of scheduler invariants |
| CSpace complexity leads to capability leaks | High | Low | Implement revocation tests early; test MDB invariants |

---

## Resource Estimates

| Phase | Estimated LOC (Simple) | Estimated LOC (Tests) | Status |
|-------|----------------------|----------------------|--------|
| Phase 0: Reorganize | -- | -- | COMPLETE |
| Phase 1: Boot + Serial | ~500 | ~100 | COMPLETE |
| Phase 2: Kernel Core x86 | ~3,000 | ~1,000 | COMPLETE |
| Phase 3: Multi-Arch | ~5,000 | ~2,000 | COMPLETE |
| Phase 4: Binary Optimization | ~1,000 | ~500 | BLOCKED |
| Future: VP + Hardening | ~6,000 | ~2,500 | Not started |
| **Total** | **~15,500** | **~6,100** | -- |

---

## Dependencies

| Dependency | Required By | Status |
|------------|-------------|--------|
| Simple compiler baremetal target | Phase 4 | **BLOCKED** (semantic error bug) |
| Simple nogc_async_mut_noalloc stdlib | Phase 1 | Available |
| SFFI for inline assembly | Phase 1 | Available |
| Simple-to-Wasm compiler backend | Future (VP) | Not started |
| QEMU x86/ARM/RISC-V | Phase 1/3 | Available (system packages) |
