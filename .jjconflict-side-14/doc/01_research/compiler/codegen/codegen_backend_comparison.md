# Codegen Backend Comparison: Cranelift vs LLVM

**Date:** December 2024
**Status:** Research Complete
**Decision:** Recommend adding LLVM backend for 32-bit and broader architecture support

## Executive Summary

Cranelift does not support any 32-bit architectures and has no plans to add them. The ARM32 backend was removed in 2022 due to lack of maintainers. Adding LLVM as an alternative backend is the practical solution for 32-bit support and broader platform coverage.

## Current State

### Cranelift Supported Architectures

| Architecture | Status | Notes |
|-------------|--------|-------|
| x86_64 | ✅ Full | Primary target |
| aarch64 | ✅ Full | ARM64, Apple Silicon |
| riscv64 | ✅ Full | Added 2022, ~21k LOC |
| s390x | ✅ Full | IBM Z mainframe |
| **x86 (i686)** | ❌ None | No 32-bit x86 |
| **arm (armv7)** | ❌ Removed | Was incomplete, removed 2022 |
| **riscv32** | ❌ None | No 32-bit RISC-V |

### Why No 32-bit in Cranelift?

1. **ARM32 was removed** - Merged incomplete, never finished, removed due to maintenance burden
2. **No contributors** - 32-bit platforms declining in priority
3. **Technical complexity** - Requires 64→32 bit legalizations across entire codebase
4. **ISLE migration** - New backends must use ISLE DSL, significant learning curve

## Option 1: Implement Cranelift 32-bit Backend

### Effort Estimate

| Component | Lines of Code | Complexity |
|-----------|---------------|------------|
| Instruction definitions | ~8,000 | High |
| ISLE lowering rules | ~6,000 | Very High |
| ABI implementation | ~3,000 | High |
| Register allocator integration | ~2,000 | Medium |
| Tests | ~2,000 | Medium |
| **Total** | **~21,000** | **Very High** |

Based on riscv64 contribution which was "about 21k lines of code, contributed by an outside developer."

### Skills Required

- **ISLE DSL** - Cranelift's pattern-matching domain-specific language
- **regalloc2** - Register allocation algorithm
- **Target ISA** - Deep knowledge of x86, ARM, or RISC-V instruction sets
- **Cranelift internals** - IR, lowering passes, ABI handling

### Timeline

- Experienced compiler engineer: 6-12 months
- Learning curve for ISLE/regalloc2: 2-3 months additional
- Ongoing maintenance commitment required

### Risks

- ARM32 was removed because "no one is using or maintaining it"
- Cranelift team may not accept incomplete backends
- 32-bit platforms declining in importance

### References

- [ARM32 backend removal discussion](https://github.com/bytecodealliance/wasmtime/issues/3721)
- [Cranelift 2022 Roadmap](https://github.com/bytecodealliance/rfcs/blob/main/accepted/cranelift-roadmap-2022.md)
- [New Backend for Cranelift (Mozilla)](https://hacks.mozilla.org/2020/10/a-new-backend-for-cranelift-part-1-instruction-selection/)

## Option 2: Add LLVM Backend (Recommended)

### Overview

Use [Inkwell](https://github.com/TheDan64/inkwell) or [llvm-sys](https://github.com/tari/llvm-sys.rs) to add LLVM as an alternative codegen backend.

### LLVM Supported Architectures

| Architecture | 32-bit | 64-bit |
|-------------|--------|--------|
| x86 | ✅ i686 | ✅ x86_64 |
| ARM | ✅ armv7 | ✅ aarch64 |
| RISC-V | ✅ riscv32 | ✅ riscv64 |
| MIPS | ✅ mips | ✅ mips64 |
| PowerPC | ✅ ppc | ✅ ppc64 |
| WebAssembly | ✅ wasm32 | ✅ wasm64 |
| And many more... | | |

### Effort Estimate

| Component | Lines of Code | Complexity |
|-----------|---------------|------------|
| MIR → LLVM IR translation | ~2,000 | Medium |
| Type mapping | ~500 | Low |
| Function signatures/ABI | ~800 | Medium |
| Runtime FFI integration | ~500 | Low |
| JIT support (optional) | ~1,000 | Medium |
| Tests | ~500 | Low |
| **Total** | **~5,000** | **Medium** |

### Inkwell vs llvm-sys

| Aspect | Inkwell | llvm-sys |
|--------|---------|----------|
| Safety | Safe Rust API | Raw C bindings |
| Ergonomics | High-level, idiomatic | Low-level |
| Maintenance | Actively maintained | Stable |
| Learning curve | Lower | Higher |
| Flexibility | Some limitations | Full LLVM access |

**Recommendation:** Use Inkwell for safer, faster development.

### Timeline

- Initial implementation: 2-3 weeks
- Testing and refinement: 1-2 weeks
- Total: **3-5 weeks**

### Dependencies

```toml
[dependencies]
inkwell = { version = "0.5", features = ["llvm18-0"] }
# OR for raw bindings:
# llvm-sys = "180"
```

### Pros

1. **All architectures** - Every platform LLVM supports
2. **Mature optimization** - Decades of optimization passes
3. **Well documented** - Extensive LLVM documentation
4. **Active community** - Large ecosystem
5. **Both JIT and AOT** - Full flexibility

### Cons

1. **Large dependency** - LLVM is ~20M lines of code
2. **Slower compilation** - ~10x slower than Cranelift
3. **Complex build** - LLVM build can be tricky
4. **Version management** - Must match LLVM versions

### References

- [Inkwell GitHub](https://github.com/TheDan64/inkwell)
- [Create Your Own Programming Language with Rust](https://createlang.rs/01_calculator/basic_llvm.html)
- [llvm-sys crate](https://crates.io/crates/llvm-sys)

## Performance Comparison

### Compilation Speed

| Backend | Time | Relative |
|---------|------|----------|
| Cranelift | 72 μs | 1x (baseline) |
| LLVM -O0 | 821 μs | 11x slower |
| LLVM -O2 | ~2-5 ms | 30-70x slower |

### Generated Code Quality

| Backend | Execution Time | Relative |
|---------|----------------|----------|
| LLVM -O2 | 1.79 ns | 1x (baseline) |
| Cranelift | 2.36 ns | 1.3x slower |
| LLVM -O0 | ~3-4 ns | 2x slower |

### Binary Size

| Backend | Size | Notes |
|---------|------|-------|
| Cranelift | Smaller | Minimal runtime |
| LLVM | Larger | More metadata |

## Proposed Architecture

```
Source Code (.spl)
       │
       ▼
   ┌─────────┐
   │ Parser  │ → AST
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │   HIR   │ → Type-checked IR
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │   MIR   │ → Platform-independent IR
   └────┬────┘
        │
    ┌───┴───┐
    ▼       ▼
┌────────┐ ┌──────────┐
│Cranelift│ │   LLVM   │  ← Backend selection
│ Backend │ │ Backend  │
└────┬────┘ └────┬─────┘
     │           │
     │    ┌──────┴──────┐
     │    ▼             ▼
     │  32-bit        64-bit
     │  targets       targets
     │
     └────► 64-bit only
            (x86_64, aarch64, riscv64)
```

### Backend Selection Strategy

```rust
pub enum CodegenBackend {
    /// Fast compilation, 64-bit only
    Cranelift,
    /// Slower compilation, all platforms, better optimization
    Llvm { opt_level: OptLevel },
}

impl CodegenBackend {
    pub fn for_target(target: Target) -> Self {
        if target.arch.is_32bit() {
            // Must use LLVM for 32-bit
            CodegenBackend::Llvm { opt_level: OptLevel::Default }
        } else {
            // Prefer Cranelift for 64-bit (faster compile)
            CodegenBackend::Cranelift
        }
    }
}
```

## Implementation Plan

### Phase 1: LLVM Backend Foundation (Week 1-2)

1. Add Inkwell dependency
2. Create `src/compiler/src/codegen/llvm.rs`
3. Implement MIR → LLVM IR translation for basic types
4. Support function definitions and calls

### Phase 2: Complete MIR Coverage (Week 2-3)

1. Control flow (if, match, loops)
2. Memory operations (alloc, load, store)
3. Collections (array, tuple, dict)
4. Closures and objects

### Phase 3: Runtime Integration (Week 3-4)

1. FFI function declarations
2. Runtime library linking
3. GC integration points

### Phase 4: Testing and Optimization (Week 4-5)

1. Cross-platform testing
2. Optimization passes
3. Performance tuning
4. Documentation

## Conclusion

**Recommendation: Add LLVM backend**

| Factor | Cranelift 32-bit | LLVM Backend |
|--------|------------------|--------------|
| Effort | ~21,000 LOC | ~5,000 LOC |
| Timeline | 6-12 months | 3-5 weeks |
| Risk | High (may be rejected) | Low |
| Maintenance | Uncertain | LLVM is stable |
| Platform coverage | 3 new targets | All platforms |
| Optimization | Limited | Excellent |

The LLVM backend provides better ROI: less effort, more platforms, better optimization, and lower maintenance burden.

## Appendix: Cranelift Version Info

Current project uses Cranelift 0.116 with `all-arch` feature enabled:

```toml
cranelift-codegen = { version = "0.116", features = ["std", "unwind", "all-arch"] }
```

This enables x86_64, aarch64, riscv64, and s390x backends.
