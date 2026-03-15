# Simple OS - Virtual Process Design (Phase 3 Stub)

**Version:** 0.1.0
**Status:** Stub / Preliminary
**Last Updated:** 2026-03-15

---

## 1. Overview

Virtual Processes (VPs) provide software-isolated execution within a shared address space, complementing the hardware-isolated Physical Processes. VPs enable lightweight, high-density process creation without the overhead of MMU context switches.

This document outlines the three planned VP execution models. Detailed design will be completed during Phase 3 implementation.

---

## 2. Motivation

Physical processes provide strong isolation via MMU page tables, but:
- Context switch cost includes TLB flush (~1000+ cycles on x86)
- Each process requires its own page tables (memory overhead)
- Maximum concurrent processes limited by physical memory for page tables

Virtual processes address these limitations:
- Context switch is a function call or register swap (~50-100 cycles)
- Shared address space, no TLB flush
- Support for 1000+ concurrent VPs in a single address space
- Suitable for fine-grained microservices, plugin systems, and IoT devices with limited memory

---

## 3. VP Execution Models

### 3.1 Wasm Path (WebAssembly)

**Approach:** Compile Simple source to WebAssembly bytecode, execute in an embedded Wasm runtime.

**Isolation mechanism:**
- Wasm's linear memory model restricts access to a single contiguous memory region
- All memory accesses are bounds-checked by the Wasm runtime
- Function calls go through an indirect call table (no arbitrary code execution)
- No direct access to host memory or system calls; all interaction through imported functions

**Trade-offs:**
- Strong sandboxing guarantees (well-studied, formally specified)
- Moderate performance (interpreted: ~10x slowdown; JIT: ~2x slowdown)
- Requires a Wasm runtime to be embedded in the kernel or a supervisor process

**Planned implementation:**
- Simple-to-Wasm compiler backend (reuse existing Simple compiler infrastructure)
- Minimal Wasm interpreter in Simple (Phase 3a)
- Optional JIT compilation for performance-critical VPs (Phase 4)

### 3.2 SFI Path (Software Fault Isolation)

**Approach:** Compile Simple to native machine code with inserted software guard instructions that restrict memory access and control flow.

**Isolation mechanism:**
- Every memory load/store is preceded by a mask instruction: `addr = addr & region_mask | region_base`
- This clamps all addresses to the VP's designated memory region
- Indirect jumps are similarly masked to prevent escaping the VP's code region
- System calls go through a verified trampoline

**Trade-offs:**
- Near-native performance (~5-15% overhead from guard instructions)
- Weaker guarantees than Wasm (correctness depends on the SFI compiler being correct)
- Architecture-specific implementation required for each target

**Planned implementation:**
- SFI instrumentation pass in the Simple compiler backend
- Verifier that checks compiled code before loading (defense in depth)
- Per-architecture guard instruction selection (x86: AND+OR, ARM: BIC+ORR, RISC-V: AND+OR)

### 3.3 Simple-Native Path (Bytecode Interpretation)

**Approach:** Execute Simple bytecode directly in a sandboxed interpreter that enforces memory and capability constraints.

**Isolation mechanism:**
- The interpreter controls all memory access -- no direct hardware memory operations
- Capability checks are performed by the interpreter on every resource access
- The bytecode format does not include raw pointers or unsafe operations
- Stack and heap bounds are enforced by the interpreter runtime

**Trade-offs:**
- Strongest isolation (interpreter has complete control)
- Slowest execution (~50-100x slowdown vs native)
- Simplest to implement (reuse the existing Simple interpreter)
- Best suited for configuration scripts, policy engines, and non-performance-critical tasks

**Planned implementation:**
- Extend the existing Simple interpreter with sandbox constraints
- Add memory budget enforcement (limit heap size per VP)
- Add instruction budget enforcement (limit CPU time per VP invocation)

---

## 4. VP Kernel Integration

### 4.1 Capability Model

VPs participate in the same capability system as physical processes:
- Each VP has its own CSpace (or a partitioned section of the host's CSpace)
- IPC between VPs and physical processes uses the same Endpoint/Notification mechanisms
- VP capabilities are subject to the same rights and revocation rules

### 4.2 Scheduling

VPs are scheduled using the same MCS scheduler:
- Each VP has a SchedContext with budget and period
- VP execution is charged against its SchedContext budget
- For interpreted VPs, the interpreter periodically checks the budget

### 4.3 Memory Model

- Each VP has a designated memory region within the host address space
- The region is specified at VP creation time
- The VP cannot access memory outside its region (enforced by Wasm/SFI/interpreter)
- VP memory regions do not overlap

---

## 5. VP Lifecycle

```
1. Create:  Host process retypes Untyped memory into a VP object
2. Load:    Host loads VP code (Wasm module / SFI binary / Simple bytecode) into VP memory
3. Configure: Host grants capabilities to the VP via its CSpace
4. Start:   Host invokes VP, transferring control to the VP entry point
5. Run:     VP executes within its sandbox, using IPC for external communication
6. Stop:    VP exits, traps, or exhausts budget; control returns to host
7. Destroy: Host revokes VP capabilities and reclaims VP memory
```

---

## 6. Open Questions (To Be Resolved in Phase 3)

1. **VP-to-VP IPC optimization:** Should VPs in the same address space use a lighter-weight IPC path?
2. **Shared memory:** Should VPs be able to share memory regions (with appropriate capabilities)?
3. **JIT security:** If JIT compilation is used, how to prevent JIT spraying attacks?
4. **Mixed mode:** Can a VP start as interpreted and be promoted to SFI after verification?
5. **Debugging:** How to provide debugging support (breakpoints, single-step) for VPs?
6. **Migration:** Can a VP be migrated between physical processes at runtime?

---

## 7. References

- Wahbe et al., "Efficient Software-Based Fault Isolation," SOSP 1993
- Yee et al., "Native Client: A Sandbox for Portable, Untrusted x86 Native Code," IEEE S&P 2009
- Haas et al., "Bringing the Web up to Speed with WebAssembly," PLDI 2017
- Simple OS Requirements Document: REQ-PROC-006 through REQ-PROC-011
