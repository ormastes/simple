# Simple OS - Requirements Document

**Version:** 0.1.0
**Status:** Draft
**Last Updated:** 2026-03-15

---

## 1. Overview

Simple OS is a capability-based L4/exokernel hybrid microkernel RTOS written entirely in the Simple language. It combines the formally-proven security model of seL4 with the flexibility of exokernel resource management and adds a novel virtual process abstraction for safe, sandboxed execution without hardware MMU isolation.

### 1.1 Goals

- **Minimal trusted computing base (TCB):** Kernel code under 15,000 lines of Simple
- **Capability-based security:** All resource access mediated by unforgeable capabilities
- **Temporal isolation:** MCS (Mixed-Criticality Systems) scheduling with budget enforcement
- **Spatial isolation:** MMU-based process isolation for physical processes
- **Software isolation:** Wasm/SFI-based sandboxing for virtual processes
- **Multi-architecture:** x86 (32-bit primary), ARM Cortex-A, RISC-V 32
- **Real-time guarantees:** Bounded worst-case execution time (WCET) for all syscalls
- **User-space drivers:** All device drivers run as unprivileged user-space servers

### 1.2 Non-Goals

- POSIX compatibility (no POSIX API layer in kernel)
- Symmetric multiprocessing in Phase 1 (uniprocessor first)
- Dynamic kernel module loading
- In-kernel filesystem

---

## 2. Security Model

### 2.1 Capability-Based Access Control

All kernel objects are accessed exclusively through capabilities. A capability is an unforgeable token that combines an object reference with a set of access rights.

**Requirements:**

- **REQ-SEC-001:** Every kernel object shall be accessible only through a valid capability
- **REQ-SEC-002:** Capabilities shall be unforgeable -- user space cannot fabricate capability values
- **REQ-SEC-003:** Capabilities shall encode access rights (Read, Write, Grant, Revoke) as a bitmask
- **REQ-SEC-004:** The kernel shall support capability derivation (minting) with equal or reduced rights
- **REQ-SEC-005:** The kernel shall support capability revocation that transitively invalidates all derived capabilities
- **REQ-SEC-006:** The initial task shall receive capabilities to all system resources at boot
- **REQ-SEC-007:** Capability transfer between processes shall occur only via explicit IPC grant operations

### 2.2 Capability Types

The kernel shall support capabilities to the following object types:

| Type | Description |
|------|-------------|
| `CNode` | Capability storage node (container of capability slots) |
| `TCB` | Thread control block |
| `Endpoint` | Synchronous IPC endpoint |
| `Notification` | Asynchronous notification object |
| `UntypedMemory` | Raw physical memory (not yet assigned a type) |
| `Frame` | Mapped physical page frame |
| `PageTable` | Page table structure for virtual memory |
| `IRQHandler` | Hardware interrupt handler binding |
| `IOPort` | x86 I/O port access (architecture-specific) |
| `VSpace` | Virtual address space root |
| `SchedContext` | Scheduling context (MCS budget/period) |

### 2.3 CSpace Structure

- **REQ-SEC-008:** Each thread shall have a CSpace (capability space) organized as a radix tree of CNodes
- **REQ-SEC-009:** CNode size shall be a power of two (4 to 16384 slots)
- **REQ-SEC-010:** CSpace addressing shall use a guard + radix scheme for compact representation
- **REQ-SEC-011:** The kernel shall support CSpace lookup in O(log n) time

---

## 3. Inter-Process Communication (IPC)

### 3.1 Synchronous IPC (L4-Style Rendezvous)

- **REQ-IPC-001:** The kernel shall provide synchronous rendezvous IPC via Endpoint objects
- **REQ-IPC-002:** IPC shall transfer messages through a per-thread IPC buffer (4 KB)
- **REQ-IPC-003:** Messages shall consist of a tag (label + length) and up to 120 message registers
- **REQ-IPC-004:** The first N message registers (N >= 4) shall be passed in CPU registers for performance
- **REQ-IPC-005:** IPC operations shall include: Send, Recv, Call (Send+Recv), ReplyRecv
- **REQ-IPC-006:** Send shall block until a receiver is ready (or timeout expires)
- **REQ-IPC-007:** Recv shall block until a sender is ready (or timeout expires)
- **REQ-IPC-008:** Call shall atomically send and then block for a reply
- **REQ-IPC-009:** ReplyRecv shall atomically reply to the previous caller and wait for the next

### 3.2 Asynchronous Notifications

- **REQ-IPC-010:** The kernel shall provide Notification objects for asynchronous signaling
- **REQ-IPC-011:** Notifications shall use a bitmap (word-sized) for lightweight signaling
- **REQ-IPC-012:** Signal operations shall OR a badge value into the notification word
- **REQ-IPC-013:** Wait on a notification shall return and clear the accumulated signals
- **REQ-IPC-014:** A thread may bind a notification to its TCB for interrupt-style delivery

### 3.3 Fault Handling

- **REQ-IPC-015:** Thread faults (page fault, capability fault, VM fault) shall be delivered as IPC messages to the thread's designated fault handler endpoint
- **REQ-IPC-016:** The fault handler shall receive fault details in the IPC message registers
- **REQ-IPC-017:** The fault handler shall reply to resume the faulting thread

---

## 4. Scheduling

### 4.1 Fixed-Priority Preemptive Scheduling

- **REQ-SCHED-001:** The scheduler shall support 256 priority levels (0 = lowest, 255 = highest)
- **REQ-SCHED-002:** The scheduler shall always run the highest-priority runnable thread
- **REQ-SCHED-003:** Threads at the same priority shall be scheduled round-robin
- **REQ-SCHED-004:** Thread priority shall be set via the TCB capability

### 4.2 MCS Scheduling (Budget-Based Temporal Isolation)

- **REQ-SCHED-005:** Each thread shall have an associated SchedContext object
- **REQ-SCHED-006:** A SchedContext shall specify a budget (microseconds) and period (microseconds)
- **REQ-SCHED-007:** The kernel shall enforce that a thread does not exceed its budget within its period
- **REQ-SCHED-008:** When a thread exhausts its budget, it shall be descheduled until its next period
- **REQ-SCHED-009:** Budget replenishment shall occur at the start of each period
- **REQ-SCHED-010:** A thread without a SchedContext shall not be schedulable
- **REQ-SCHED-011:** SchedContext objects shall be transferable between threads for priority donation during IPC

### 4.3 Real-Time Properties

- **REQ-SCHED-012:** All system calls shall have bounded WCET
- **REQ-SCHED-013:** Interrupt latency shall be bounded and documented per architecture
- **REQ-SCHED-014:** The kernel shall be fully preemptible (no Big Kernel Lock)

---

## 5. Process Model

### 5.1 Physical Processes (Hardware-Isolated)

- **REQ-PROC-001:** Physical processes shall run in separate MMU-protected address spaces
- **REQ-PROC-002:** Each process shall have its own VSpace (page table hierarchy)
- **REQ-PROC-003:** User-space processes shall run at the lowest CPU privilege level (Ring 3 on x86, EL0 on ARM, U-mode on RISC-V)
- **REQ-PROC-004:** The kernel shall support at least 64 concurrent physical processes
- **REQ-PROC-005:** Process creation shall be performed by user space using Untyped memory retype and TCB/VSpace/CSpace configuration

### 5.2 Virtual Processes (Software-Isolated) -- Phase 3

- **REQ-PROC-006:** Virtual processes shall execute within a single address space using software fault isolation (SFI) or WebAssembly (Wasm) sandboxing
- **REQ-PROC-007:** Virtual processes shall be subject to the same capability-based access control as physical processes
- **REQ-PROC-008:** Virtual processes shall share the host process's address space but with restricted memory access
- **REQ-PROC-009:** The kernel shall support at least 1024 concurrent virtual processes
- **REQ-PROC-010:** Virtual process context switch shall be achievable in under 100 nanoseconds
- **REQ-PROC-011:** Three VP execution models shall be supported:
  - Wasm: Compile Simple to Wasm, run in embedded interpreter/JIT
  - SFI: Compile Simple to native with software guard instructions
  - Simple-native: Interpret Simple bytecode directly with sandbox constraints

---

## 6. Memory Management

### 6.1 Untyped Memory Model

- **REQ-MEM-001:** All physical memory shall initially be represented as Untyped Memory capabilities
- **REQ-MEM-002:** Untyped memory shall be converted to typed objects via the Retype operation
- **REQ-MEM-003:** Retype shall subdivide an untyped block into one or more objects of a specified type
- **REQ-MEM-004:** Retyped objects shall include: Frame, PageTable, CNode, TCB, Endpoint, Notification, SchedContext
- **REQ-MEM-005:** Retype shall fail if the untyped block has already been retyped (no double allocation)
- **REQ-MEM-006:** Revoke on an untyped capability shall destroy all objects created from it and reclaim the memory

### 6.2 Virtual Memory

- **REQ-MEM-007:** The kernel shall support 4 KB page granularity on all architectures
- **REQ-MEM-008:** The kernel shall support architecture-specific large pages (4 MB on x86, 2 MB on ARM, 4 MB on RISC-V)
- **REQ-MEM-009:** Page mapping shall require both a Frame capability and a VSpace/PageTable capability
- **REQ-MEM-010:** Page access permissions shall be derived from the intersection of the Frame capability rights and the mapping rights

### 6.3 Kernel Memory

- **REQ-MEM-011:** The kernel shall not dynamically allocate memory after boot
- **REQ-MEM-012:** All kernel objects shall be allocated from user-provided Untyped memory via Retype
- **REQ-MEM-013:** The kernel shall have a fixed-size boot-time allocation for its own data structures

---

## 7. Hardware Abstraction

### 7.1 Multi-Architecture Support

- **REQ-ARCH-001:** The kernel shall support x86 (i686, 32-bit protected mode) as the primary target
- **REQ-ARCH-002:** The kernel shall support ARM Cortex-A (ARMv7-A, 32-bit) as a secondary target
- **REQ-ARCH-003:** The kernel shall support RISC-V (RV32IMA) as a tertiary target
- **REQ-ARCH-004:** Architecture-specific code shall be isolated in `arch/<arch>/` directories
- **REQ-ARCH-005:** The kernel core shall be architecture-independent

### 7.2 Interrupts

- **REQ-INT-001:** Hardware interrupts shall be delivered to user-space handlers via Notification objects
- **REQ-INT-002:** Each IRQ line shall have an associated IRQHandler capability
- **REQ-INT-003:** The IRQHandler capability holder shall be able to acknowledge interrupts
- **REQ-INT-004:** Interrupt priorities shall be mappable to thread scheduling priorities

### 7.3 User-Space Drivers

- **REQ-DRV-001:** All device drivers shall run as user-space processes
- **REQ-DRV-002:** Drivers shall access device memory via Frame capabilities mapped to MMIO regions
- **REQ-DRV-003:** On x86, drivers shall access I/O ports via IOPort capabilities
- **REQ-DRV-004:** Drivers shall receive interrupts via bound Notification objects

---

## 8. System Call Interface

### 8.1 System Call List

The kernel shall expose the following system calls:

| Syscall | Description |
|---------|-------------|
| `sys_send` | Send message to endpoint |
| `sys_recv` | Receive message from endpoint |
| `sys_call` | Send and wait for reply |
| `sys_reply_recv` | Reply and wait for next message |
| `sys_signal` | Signal a notification |
| `sys_wait` | Wait on a notification |
| `sys_yield` | Voluntarily yield CPU |
| `sys_retype` | Convert untyped memory to typed objects |
| `sys_cnode_copy` | Copy a capability |
| `sys_cnode_mint` | Mint a capability with reduced rights |
| `sys_cnode_delete` | Delete a capability |
| `sys_cnode_revoke` | Revoke a capability and all descendants |
| `sys_tcb_configure` | Configure thread control block |
| `sys_tcb_set_priority` | Set thread priority |
| `sys_tcb_resume` | Resume a suspended thread |
| `sys_tcb_suspend` | Suspend a thread |
| `sys_vspace_map` | Map a frame into an address space |
| `sys_vspace_unmap` | Unmap a frame |
| `sys_irq_set_handler` | Bind IRQ to notification |
| `sys_irq_ack` | Acknowledge interrupt |
| `sys_sched_context_configure` | Configure MCS budget/period |
| `sys_debug_putchar` | Debug: write character to serial (debug builds only) |

- **REQ-SYS-001:** All system calls shall validate capabilities before performing operations
- **REQ-SYS-002:** System call arguments shall be passed in registers (no user-space pointer dereference for arguments)
- **REQ-SYS-003:** System calls shall return a status code indicating success or error type
- **REQ-SYS-004:** Total system call count shall not exceed 24

---

## 9. Boot Requirements

- **REQ-BOOT-001:** The kernel shall boot from a Multiboot-compliant bootloader on x86
- **REQ-BOOT-002:** The kernel shall initialize the serial port for early debug output
- **REQ-BOOT-003:** The kernel shall enumerate available physical memory from the bootloader memory map
- **REQ-BOOT-004:** The kernel shall create Untyped memory capabilities for all available physical memory
- **REQ-BOOT-005:** The kernel shall create and start an initial task with capabilities to all resources
- **REQ-BOOT-006:** The kernel shall output "[BOOT OK]" on serial when the initial task begins execution

---

## 10. Performance Requirements

- **REQ-PERF-001:** IPC round-trip (call + reply) shall complete in under 1000 cycles on x86
- **REQ-PERF-002:** Context switch shall complete in under 500 cycles on x86
- **REQ-PERF-003:** Capability lookup shall complete in under 200 cycles for a 2-level CSpace
- **REQ-PERF-004:** System call entry/exit overhead shall be under 100 cycles on x86
- **REQ-PERF-005:** Interrupt dispatch to user-space handler shall complete in under 2000 cycles

---

## 11. Testing Requirements

- **REQ-TEST-001:** All kernel data structures shall have unit tests runnable in hosted mode
- **REQ-TEST-002:** Integration tests shall run on QEMU with automated serial output verification
- **REQ-TEST-003:** Boot smoke test shall verify kernel reaches initial task on all target architectures
- **REQ-TEST-004:** IPC tests shall verify message passing between two user-space tasks
- **REQ-TEST-005:** Capability tests shall verify access control enforcement (unauthorized access is denied)

---

## 12. Traceability Matrix

| Requirement Group | Count | Phase |
|-------------------|-------|-------|
| Security (SEC) | 11 | 1 |
| IPC | 17 | 1 |
| Scheduling (SCHED) | 14 | 1-2 |
| Process (PROC) | 5 phys + 6 virt | 1, 3 |
| Memory (MEM) | 13 | 1 |
| Architecture (ARCH) | 5 | 1-2 |
| Interrupts (INT) | 4 | 1 |
| Drivers (DRV) | 4 | 2 |
| System Calls (SYS) | 4 | 1 |
| Boot (BOOT) | 6 | 1 |
| Performance (PERF) | 5 | 2 |
| Testing (TEST) | 5 | 1 |
