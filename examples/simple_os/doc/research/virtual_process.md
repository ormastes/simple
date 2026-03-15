# Simple OS - Virtual Process Research

**Version:** 0.1.0
**Last Updated:** 2026-03-15

---

## 1. Overview

This document surveys sandboxing and isolation techniques relevant to Simple OS Virtual Processes (VPs). VPs provide software-based isolation within a shared address space, complementing hardware-based MMU isolation used by Physical Processes.

Three isolation approaches are evaluated: WebAssembly (Wasm), Software Fault Isolation (SFI), and language-based isolation.

---

## 2. WebAssembly (Wasm) Sandboxing

### 2.1 Background

WebAssembly is a portable bytecode format originally designed for web browsers but increasingly used for server-side and embedded sandboxing. Its design provides strong isolation guarantees by construction.

### 2.2 Security Model

**Linear memory isolation:**
- Each Wasm module has a single linear memory (a contiguous byte array)
- All memory accesses are bounds-checked against the linear memory size
- No raw pointers -- memory addresses are offsets into the linear memory
- Out-of-bounds access traps immediately

**Control flow integrity:**
- Function calls go through an indirect call table with type checking
- No arbitrary jumps -- all control flow targets are validated
- Call stack is separate from linear memory (cannot be corrupted)

**Host interface:**
- Wasm modules cannot access host memory or system calls directly
- All external interaction goes through explicitly imported functions
- The host controls which functions are available to the module

### 2.3 Performance Characteristics

| Execution Mode | Overhead vs Native | Startup Time |
|----------------|-------------------|--------------|
| Interpreter | 10-50x slower | < 1ms |
| Baseline JIT | 2-5x slower | 1-10ms |
| Optimizing JIT | 1.1-2x slower | 10-100ms |
| AOT compiled | 1.05-1.5x slower | < 1ms (pre-compiled) |

### 2.4 Existing Wasm Runtimes

| Runtime | Language | Size | JIT | AOT | Embedded-friendly |
|---------|----------|------|-----|-----|-------------------|
| Wasmtime | Rust | ~2MB | Yes | Yes | Moderate |
| Wasmer | Rust | ~2MB | Yes | Yes | Moderate |
| wasm3 | C | ~60KB | No (interpreter) | No | Yes |
| WAMR | C | ~50KB | Yes (fast JIT) | Yes | Yes |
| Wasm Micro Runtime | C | ~30KB | Optional | Optional | Yes |

**Recommendation for Simple OS:** Start with an interpreter (~30-60KB overhead), add AOT compilation later. wasm3's threaded-interpreter approach achieves ~10x overhead with minimal code size.

### 2.5 Wasm for Kernel Use

Key considerations:
- Wasm spec is well-defined and stable (no ambiguity in semantics)
- Wasm modules can be validated in linear time before execution
- No need for MMU -- isolation is purely in software
- Deterministic execution (no UB, no uninitialized memory)
- Resource metering can be added via instruction counting

Challenges:
- Wasm does not natively support capabilities (must be layered on top)
- GC-less operation requires careful memory management in the Wasm module
- Multi-threading support (Wasm threads proposal) adds complexity
- Floating-point operations may need to be restricted or emulated for determinism in RTOS

### 2.6 Simple-to-Wasm Compilation

The Simple compiler can target Wasm by:
1. Compiling Simple source to Simple IR
2. Lowering Simple IR to Wasm bytecode
3. Mapping Simple types to Wasm types (Int -> i32/i64, Float -> f32/f64)
4. Mapping Simple function calls to Wasm function indices
5. Mapping Simple heap allocation to Wasm linear memory management
6. Exposing kernel IPC as imported host functions

---

## 3. Software Fault Isolation (SFI)

### 3.1 Background

SFI (Wahbe et al., 1993) instruments native code at compile time to restrict memory access to a designated region. Every memory operation is preceded by masking instructions that clamp the address to the allowed range.

### 3.2 Classic SFI (Sandboxing via Address Masking)

**Basic approach:**
```
# Before every load/store:
# Restrict address to sandbox region [base, base + size)
address = (address & mask) | base

# Where:
#   mask = size - 1  (size must be power of 2)
#   base = start address of sandbox region
```

This ensures every memory access falls within the designated region, regardless of the address computed by the sandboxed code.

**Code example (x86):**
```
# Original: mov eax, [ecx]
# SFI-instrumented:
and ecx, 0x0FFFFFFF    # Mask to 256MB region
or  ecx, 0x10000000    # Set base to 0x10000000
mov eax, [ecx]          # Now guaranteed in [0x10000000, 0x1FFFFFFF]
```

### 3.3 Google Native Client (NaCl)

NaCl (2009) refined SFI for x86:
- 32-byte aligned code bundles (no instruction spans a bundle boundary)
- All indirect jumps masked to bundle-aligned targets
- Segment-based sandboxing on x86-32 (zero overhead for data access)
- Validator verifies compiled code before execution

Performance overhead: 5-7% on SPEC benchmarks.

### 3.4 ARM SFI

ARM SFI uses different techniques:
- BIC (bit clear) instruction for address masking (single instruction)
- Branch masking for indirect control flow
- No segment registers available -- must use explicit masking

```
# ARM SFI address masking:
bic r0, r0, #0xF0000000    # Clear top 4 bits
orr r0, r0, #0x20000000    # Set base region
ldr r1, [r0]                # Sandboxed load
```

### 3.5 RISC-V SFI

RISC-V SFI:
- AND + OR instruction pair for address masking
- No special hardware support needed
- Straightforward implementation

```
# RISC-V SFI address masking:
and a0, a0, t0    # t0 = mask (pre-loaded)
or  a0, a0, t1    # t1 = base (pre-loaded)
lw  a1, 0(a0)     # Sandboxed load
```

### 3.6 SFI Performance

| Architecture | Masking Overhead | Instructions per Load/Store | Typical Benchmark Overhead |
|-------------|-----------------|----------------------------|--------------------------|
| x86-32 (segment) | 0% (data) | 0 | 2-5% |
| x86-32 (mask) | ~10% | 2 | 7-15% |
| ARM | ~8% | 2 | 5-12% |
| RISC-V | ~10% | 2 | 8-15% |

### 3.7 SFI Verification

A critical component of SFI security is a verifier that checks compiled code:
- Validates that every memory access is preceded by masking instructions
- Validates that no indirect jump can bypass masking
- Validates that no instruction crosses a bundle boundary (NaCl-style)
- Runs in linear time over the code

The verifier is part of the TCB -- it must be correct for SFI to be secure.

### 3.8 SFI Limitations

- **Architecture-specific:** Each target needs its own masking strategy
- **Compiler trust:** The SFI compiler must insert all guards correctly
- **Verifier complexity:** The verifier is non-trivial and must be bug-free
- **Code density:** Masking instructions increase code size by ~15-30%
- **Self-modifying code:** Not supported (JIT requires special handling)

---

## 4. Language-Based Isolation

### 4.1 Concept

Instead of hardware (MMU) or binary (SFI) isolation, use the programming language's type system and runtime to enforce isolation. A safe language runtime prevents:
- Buffer overflows (bounds checking)
- Use-after-free (ownership or GC)
- Type confusion (static typing)
- Arbitrary pointer arithmetic (no raw pointers)

### 4.2 Singularity OS (Microsoft Research)

Singularity (2005-2010) demonstrated language-based isolation:
- Entire OS written in Sing# (a safe C# dialect)
- Processes run in the same address space (no MMU isolation)
- Type safety enforced by the compiler prevents cross-process interference
- Contract-based channels for IPC (statically verified protocols)
- No MMU context switches -- process isolation at ~zero overhead

Lessons for Simple OS:
- Language-based isolation works in practice
- Requires the entire software stack to be in the safe language
- Inter-process channels can be statically verified
- Performance is excellent (no MMU overhead)

### 4.3 Simple Language Properties for Isolation

Simple's type system provides several isolation-relevant guarantees:
- **No raw pointers:** Memory accessed through typed references
- **Bounds checking:** Array/list access is bounds-checked
- **Ownership:** Simple's ownership model prevents use-after-free
- **No unsafe:** No escape hatch to bypass type system safety
- **Immutable by default:** `val` declarations prevent mutation

These properties make Simple suitable for language-based isolation:
- A Simple bytecode interpreter can enforce all safety invariants
- The interpreter acts as a reference monitor for memory and capability access
- No need for SFI masking or Wasm bounds checks -- the language prevents violations

### 4.4 Comparison

| Property | Wasm | SFI | Language-Based |
|----------|------|-----|---------------|
| Performance | Moderate (2-10x) | Near-native (1.05-1.15x) | Slow (10-100x interp.) |
| Security strength | Strong (well-specified) | Moderate (verifier-dependent) | Strong (type-system-based) |
| Implementation effort | High (need Wasm runtime) | Moderate (compiler pass) | Low (extend interpreter) |
| Code portability | High (Wasm is arch-neutral) | Low (arch-specific) | High (bytecode is portable) |
| Memory overhead | Moderate (runtime) | Low (just masking) | Low-Moderate (interpreter) |
| Startup time | Fast (interp.) / Slow (JIT) | Fast (pre-compiled) | Fast (interpreter ready) |
| Debugging | Good (source maps) | Hard (binary-level) | Excellent (interpreter control) |

---

## 5. Hybrid Approach for Simple OS

### 5.1 Recommended Strategy

Simple OS should support all three isolation modes, chosen per VP based on requirements:

| Use Case | Recommended Mode | Rationale |
|----------|-----------------|-----------|
| Performance-critical services | SFI | Near-native speed |
| Untrusted third-party code | Wasm | Strongest sandboxing, well-studied |
| Configuration / scripting | Simple-native (interpreter) | Easiest to implement, best debugging |
| Prototyping | Simple-native | Fastest iteration cycle |
| Production drivers | SFI | Performance matters for drivers |

### 5.2 Unified VP Interface

Regardless of execution mode, all VPs share the same kernel interface:
- Same CSpace and capability model
- Same IPC mechanism (Endpoints and Notifications)
- Same scheduling (MCS SchedContext)
- Same memory accounting (Untyped retype)

The VP execution mode is an implementation detail hidden behind a uniform `VirtualProcess` kernel object.

### 5.3 Implementation Priority

1. **Phase 3a:** Simple-native interpreter (lowest effort, validates VP design)
2. **Phase 3b:** Wasm interpreter (strong sandboxing, portable)
3. **Phase 3c:** SFI compiler pass (near-native performance)
4. **Phase 4:** Wasm AOT/JIT (performance optimization)

---

## 6. Security Analysis

### 6.1 Threat Model

- **Untrusted VP code:** May attempt to access memory outside its region, invoke unauthorized system calls, or disrupt other VPs
- **Trusted kernel and host process:** The kernel and the process hosting VPs are in the TCB
- **VP capabilities:** VPs should only access resources explicitly granted via capabilities

### 6.2 Attack Vectors and Mitigations

| Attack | Wasm Mitigation | SFI Mitigation | Interpreter Mitigation |
|--------|----------------|----------------|----------------------|
| Buffer overflow | Linear memory bounds | Address masking | Bounds checking |
| Code injection | No writable+executable memory | Code verification | No native code execution |
| ROP/JOP | Structured control flow | Bundle alignment + jump masking | No native code execution |
| Side channels | Timing normalization | Architecture-specific | Instruction-level control |
| Resource exhaustion | Instruction metering | Timer-based preemption | Instruction metering |
| Capability forgery | Host-mediated capability access | Same | Interpreter-enforced checks |

---

## 7. References

1. Wahbe, R. et al. "Efficient Software-Based Fault Isolation." SOSP 1993.
2. Yee, B. et al. "Native Client: A Sandbox for Portable, Untrusted x86 Native Code." IEEE S&P 2009.
3. Haas, A. et al. "Bringing the Web up to Speed with WebAssembly." PLDI 2017.
4. Hunt, G. et al. "An Overview of the Singularity Project." Microsoft Research TR-2005-135.
5. Morrisett, G. et al. "From System F to Typed Assembly Language." POPL 1998.
6. Sehr, D. et al. "Adapting Software Fault Isolation to Contemporary CPU Architectures." USENIX Security 2010.
7. Lucet Contributors. "Lucet: A Native WebAssembly Compiler and Runtime." Fastly, 2019.
8. wasm3 Contributors. "wasm3: A Fast WebAssembly Interpreter." https://github.com/user/wasm3
