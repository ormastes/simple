# Simple OS - Research Findings

**Version:** 0.1.0
**Last Updated:** 2026-03-15

---

## 1. L4 Microkernel Family Comparison

### 1.1 Overview

The L4 family represents the state-of-the-art in microkernel design, evolving from Jochen Liedtke's original L4 (1993) through several generations of refinement.

### 1.2 Comparison Table

| Feature | L4Ka::Pistachio | OKL4 | Fiasco.OC | seL4 | NOVA | Simple OS (planned) |
|---------|----------------|------|-----------|------|------|---------------------|
| **IPC model** | Sync rendezvous | Sync + async | Sync + async | Sync + notifications | Portal-based | Sync + notifications |
| **Security model** | Spaces + clans | Spaces | Capabilities (basic) | Capabilities (full) | Capabilities | Capabilities (full) |
| **Scheduling** | Fixed priority | Fixed priority | Fixed priority | MCS | Fixed priority | Fixed priority + MCS |
| **Memory model** | Sigma0/Sigma1 | Flex pages | Flex pages | Untyped retype | Untyped-like | Untyped retype |
| **Formal verification** | No | No | No | Yes (C/ARM) | No | No (but designed for) |
| **Multi-arch** | x86, MIPS, ARM, PowerPC, Alpha | ARM, MIPS, x86 | x86, ARM, MIPS | x86, ARM, RISC-V | x86 (64-bit) | x86, ARM, RISC-V |
| **Lines of code** | ~40K | ~10K | ~70K | ~10K (C+ASM) | ~9K | Target: <15K |
| **Real-time** | Soft | Soft | Soft | Hard (MCS) | Soft | Hard (MCS) |
| **Language** | C++ | C | C++ | C + Isabelle/HOL | C++ | Simple |
| **SMP support** | Yes | Yes | Yes | Yes | Yes | No (Phase 1) |

### 1.3 Key Takeaways

**From L4Ka::Pistachio:**
- Clean IPC ABI design with register-based message passing
- Importance of fast-path optimization (critical for IPC performance)
- Recursive address space model (Sigma0 protocol) -- we adopt a simpler Untyped model instead

**From OKL4:**
- Commercial-grade microkernel proves viability for mobile/embedded
- Importance of small kernel footprint for embedded targets
- Cap-based security can be added to L4 without sacrificing performance

**From Fiasco.OC:**
- Hybrid capability model shows capabilities are compatible with L4 IPC
- IPC gate abstraction simplifies endpoint management
- Kernel object factory pattern (similar to our Retype)

**From seL4:**
- Formal verification is achievable for a real microkernel
- Untyped retype model eliminates kernel memory allocation after boot
- MCS scheduling provides temporal isolation for mixed-criticality systems
- Capability derivation tree (MDB) enables clean revocation
- **Primary design influence for Simple OS**

**From NOVA:**
- Minimalism taken to extreme (~9K lines) proves small kernels are viable
- Portal-based IPC is an interesting alternative but more complex than endpoints
- Demonstrates that capability-based security has negligible performance overhead

---

## 2. seL4 Capability Model Deep Dive

### 2.1 Capability Structure

seL4 capabilities are stored in CNodes (Capability Nodes). Each capability is a 2-word (64-bit on 32-bit arch, 128-bit on 64-bit arch) structure:

```
Word 0: [type:5 | cap-specific-data:27]
Word 1: [cap-specific-data continued]
```

The type field identifies the kernel object type. The remaining bits encode object-specific information (pointer, rights, badge, guard, etc.).

### 2.2 CSpace Organization

seL4's CSpace is a radix tree of CNodes with guard compression:

- **Guard:** A fixed bit pattern that must match during lookup (compresses sparse trees)
- **Radix:** The number of index bits consumed at this CNode level
- **Depth:** Total bits consumed = sum of (guard_bits + radix_bits) at each level

This allows a single CNode to serve as a flat capability table (guard=0, large radix) or a multi-level tree (small radix, multiple levels).

**Design decision for Simple OS:** Adopt the same guard+radix CSpace model. It provides good flexibility and space efficiency.

### 2.3 Mapping Database (MDB)

seL4 tracks capability derivation in a sorted doubly-linked list called the MDB:

- All capabilities to the same object are contiguous
- Sorted by object address and derivation depth
- Enables efficient revocation: walk the MDB to find and delete all derived caps
- Revocation of an Untyped cap destroys all objects created from that memory

**Design decision for Simple OS:** Use the same MDB approach. The linked-list representation is simple and sufficient for our needs.

### 2.4 Untyped Memory

seL4's most innovative memory management idea:

1. All physical memory starts as Untyped capabilities
2. The Retype operation carves typed objects from Untyped memory
3. The kernel never allocates memory itself (no kernel heap)
4. Memory can only be reclaimed by revoking the parent Untyped capability

Benefits:
- No memory allocation failures in the kernel
- Complete user-space control over memory distribution
- Clean resource accounting (every byte is tracked by capabilities)

**Design decision for Simple OS:** Adopt Untyped retype wholesale. This is one of seL4's best ideas.

### 2.5 Fault Handling

seL4 delivers thread faults as IPC messages to a designated fault handler:

- Page faults: delivered with fault address, instruction/data flag, and FSR
- Capability faults: delivered when a thread invokes an invalid capability
- The fault handler replies to resume the faulting thread

This unifies exception handling with the IPC mechanism, keeping the kernel simple.

**Design decision for Simple OS:** Adopt the same fault-as-IPC model.

---

## 3. Scheduling Approaches

### 3.1 Fixed-Priority Preemptive (Traditional L4)

Most L4 implementations use a simple fixed-priority round-robin scheduler:
- 256 priority levels
- Highest-priority runnable thread always runs
- Same-priority threads round-robin with a fixed time quantum
- Simple, predictable, low overhead (~50 cycles for scheduling decision)

Limitations:
- No temporal isolation: a high-priority thread can starve lower-priority threads
- Priority inversion possible without explicit handling
- No budget enforcement for untrusted code

### 3.2 MCS Scheduling (seL4 Approach)

seL4's Mixed-Criticality Systems (MCS) extension adds:
- **Scheduling Contexts:** First-class objects with budget and period
- **Budget enforcement:** A thread cannot exceed its budget in a period
- **Passive threads:** Threads without a SchedContext cannot run
- **Priority donation:** SchedContext can be lent during IPC (solves priority inversion)

Performance impact:
- seL4 benchmarks show MCS adds ~5-10% overhead to IPC
- Timer interrupt handling is slightly more complex (budget tracking)
- Worth the cost for mixed-criticality and real-time systems

**Design decision for Simple OS:** Implement both. Start with fixed-priority in Phase 1, add MCS budget enforcement in Phase 2.

### 3.3 EDF (Earliest Deadline First)

Theoretically optimal for uniprocessor real-time scheduling:
- Each task has a deadline
- Scheduler always picks the task with the earliest deadline
- Achieves 100% CPU utilization (vs ~69% for Rate Monotonic)

Not adopted because:
- More complex implementation (priority queue with dynamic priorities)
- seL4 showed MCS provides sufficient temporal isolation
- Fixed-priority is simpler to reason about and more widely understood

### 3.4 Gang Scheduling / Co-Scheduling

For SMP systems, related threads can be scheduled simultaneously:
- Reduces IPC latency between threads on different cores
- More complex to implement
- Not relevant for our uniprocessor Phase 1

---

## 4. Interrupt Handling Approaches

### 4.1 Interrupt-as-IPC (L4 Tradition)

Interrupts are delivered to user-space handlers via IPC:
- Each IRQ has an associated Notification object
- Hardware interrupt signals the Notification
- User-space driver waits on the Notification
- After handling, driver acknowledges the IRQ

Benefits:
- Unified mechanism for interrupts and IPC
- User-space drivers have no special privilege
- Easy to reason about (no kernel interrupt handlers)

seL4 optimization: Notifications are lighter than full IPC -- just a bitmap OR.

**Design decision for Simple OS:** Use Notifications for interrupt delivery.

### 4.2 Interrupt Latency

Key factors:
- Time from hardware interrupt to user-space handler notification
- Depends on: interrupt controller setup, kernel preemptibility, IPC overhead
- seL4 achieves ~1000-2000 cycles on ARM Cortex-A9

For Simple OS:
- Target: <2000 cycles on x86 (interrupt to user-space handler running)
- Kernel must be fully preemptible (no long critical sections)
- Timer interrupt for MCS budget tracking must be very fast

---

## 5. Memory Management Approaches

### 5.1 Sigma0 Protocol (Classic L4)

Original L4 memory management:
- Sigma0 (root pager) owns all physical memory
- Processes request memory from Sigma0 via IPC
- Sigma0 maps pages into the requester's address space
- Recursive address spaces: any process can act as a pager for its children

Limitations:
- Complex revocation semantics
- No clear memory accounting
- Sigma0 is a single point of failure

### 5.2 Flex Pages (L4 Evolution)

Improved memory management:
- Memory transferred as "flex pages" (power-of-2 aligned regions)
- Map, Grant, and Unmap operations
- Simplified page fault handling

Still limited:
- No typed memory management
- Kernel still needs to allocate internal structures

### 5.3 Untyped Retype (seL4)

Best approach (adopted by Simple OS):
- All memory starts as Untyped capabilities
- Retype creates typed objects from Untyped
- No kernel memory allocation after boot
- Clean revocation via MDB
- Complete memory accounting

---

## 6. Formal Verification Considerations

### 6.1 seL4 Verification Approach

seL4 was verified using:
- Isabelle/HOL theorem prover
- Abstract specification -> executable specification -> C implementation
- Proved functional correctness: C code refines the abstract spec
- Also proved: integrity (no unauthorized access), confidentiality (no information leaks)

Cost: ~20 person-years for the original ARM 32-bit verification

### 6.2 Applicability to Simple OS

Simple OS is written in Simple, not C, which affects verification:
- Simple's type system provides some guarantees for free (no buffer overflows, no null pointer dereferences in safe code)
- Simple's trait system can encode invariants
- The Simple compiler could potentially generate verification conditions

Long-term goal: Explore verification using Simple's type system as a foundation. Not in scope for Phase 1-4, but the design should be "verification-friendly":
- Small, well-defined kernel API
- No global mutable state
- Clear pre/post-conditions for all kernel operations
- Bounded loops (no unbounded iteration)

---

## 7. Implementation Language Considerations

### 7.1 Why Simple?

- **No GC:** Simple supports nogc mode (critical for kernel code)
- **No heap required:** Simple can operate without dynamic allocation
- **Type safety:** Prevents common kernel bugs (buffer overflows, type confusion)
- **Trait system:** Clean abstraction for architecture HAL
- **Enum/pattern matching:** Natural for kernel object model (tagged union)
- **Self-hosting:** Writing an OS in Simple exercises and validates the language

### 7.2 Challenges

- **No inline assembly:** Need SFFI (Simple Foreign Function Interface) for hardware access
- **Compiler maturity:** The Simple compiler is still evolving
- **Performance:** Simple may not match hand-tuned C/assembly for critical paths
- **Ecosystem:** No existing OS libraries to build on

### 7.3 Mitigations

- Architecture-specific boot code can use `.shs` shell scripts for build orchestration
- Critical fast paths (IPC, context switch) can use SFFI to call optimized assembly
- Build system supports `baremetal` target presets with no runtime dependencies
- `std.nogc_async_mut_noalloc` stdlib variant provides bare-metal primitives

---

## 8. References

1. Liedtke, J. "On u-Kernel Construction." SOSP 1995.
2. Klein, G. et al. "seL4: Formal Verification of an OS Kernel." SOSP 2009.
3. Lyons, A. et al. "Scheduling-Context Capabilities: A Principled, Light-Weight Operating-System Mechanism for Managing Time." EuroSys 2018.
4. Steinberg, U. and Kauer, B. "NOVA: A Microhypervisor-Based Secure Virtualization Architecture." EuroSys 2010.
5. Heiser, G. and Leslie, B. "The OKL4 Microvisor: Convergence Point of Microkernel and Hypervisor Design." APSYS 2010.
6. seL4 Reference Manual, version 12.1.0. https://sel4.systems/Info/Docs/seL4-manual-latest.pdf
