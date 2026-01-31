# Backend Instruction Completeness - Quick Summary

**Date:** 2026-01-31
**Full Report:** `doc/research/multi_backend_instruction_completeness.md`

## TL;DR

**Problem:** How do we prevent missing instruction implementations across multiple compiler backends (Cranelift, LLVM, Vulkan)?

**Answer:** Use **exhaustive pattern matching** (compile-time safety) + **automated testing** (runtime safety net).

---

## Current Issues in Simple Compiler

### Dangerous Patterns Found

```rust
// LLVM backend: rust/compiler/src/codegen/llvm/instructions.rs
match inst {
    MirInst::ConstInt { .. } => { /* implemented */ }
    _ => {} // ⚠️ SILENTLY IGNORES UNKNOWN INSTRUCTIONS
}

// Vulkan backend: rust/compiler/src/codegen/vulkan/spirv_instructions.rs
match inst {
    MirInst::GpuBarrier => { /* implemented */ }
    _ => {} // ⚠️ SILENTLY IGNORES NON-GPU INSTRUCTIONS
}
```

**Risk:** When we add a new MirInst variant, these backends will compile successfully but silently fail to handle it.

---

## Recommended Solution

### Tier 1 (Must Implement Immediately)

#### 1. Remove All Catch-All Patterns

**Before (UNSAFE):**
```rust
match inst {
    MirInst::ConstInt { .. } => { /* ... */ }
    MirInst::BinOp { .. } => { /* ... */ }
    _ => {} // BAD
}
```

**After (SAFE):**
```rust
match inst {
    MirInst::ConstInt { .. } => { /* ... */ }
    MirInst::BinOp { .. } => { /* ... */ }

    // Explicitly list all other variants
    MirInst::GpuBarrier => {
        Err(CompileError::unsupported("LLVM backend doesn't support GPU intrinsics"))
    }
    MirInst::GpuGlobalId { .. } => {
        Err(CompileError::unsupported("LLVM backend doesn't support GPU intrinsics"))
    }
    // ... must list all 80+ variants (Rust enforces this)
}
```

**Result:** Adding new MirInst variant will cause **compile error** in every backend that doesn't handle it.

#### 2. Add Automated Coverage Tests

```rust
#[test]
fn test_llvm_handles_all_instructions() {
    let backend = LlvmBackend::new();
    for inst in MirInst::all_variants() {
        let result = backend.lower_instruction(&inst);
        // Must either succeed or return explicit unsupported error
        assert!(result.is_ok() || matches!(result, Err(CompileError::Unsupported(_))));
    }
}
```

**Result:** Tests fail if any backend silently ignores an instruction.

### Tier 2 (Should Have)

#### 3. Backend Capability Documentation

Auto-generate tables showing what each backend supports:

| Instruction | Cranelift | LLVM | Vulkan |
|-------------|-----------|------|--------|
| ConstInt    | ✅        | ✅   | ✅     |
| GpuBarrier  | ❌        | ❌   | ✅     |
| BinOp       | ✅        | ✅   | ✅     |

### Tier 3 (Future Enhancement)

#### 4. Code Generation from DSL (When We Have 150+ Instructions)

Like LLVM's TableGen or Cranelift's ISLE:
- Define instructions once in DSL
- Auto-generate enum + backend stubs
- Reduces boilerplate

**Not needed now** - current scale (80 instructions, 3 backends) is manageable with manual exhaustive matching.

---

## Why This Works

### Evidence from Major Compilers

1. **Rust/Cranelift:**
   - ISLE DSL generates exhaustive Rust match expressions
   - "As good as or better than handwritten code"
   - Provides machine-checkable verification

2. **LLVM:**
   - TableGen generates code from instruction definitions
   - Built-in verifier pass runs after every transformation
   - Heavy testing with real-world applications

3. **WebAssembly (Crocus):**
   - Even with DSL, verification still needed
   - "Instruction lowering is error-prone even for experienced engineers"

4. **MLIR:**
   - Full conversion mode: all operations must be legalized
   - Partial conversion allows silent failures (avoided by design)

### Why Not Other Approaches?

❌ **Trait with 80+ required methods:** Too rigid, breaks on MIR changes
❌ **Runtime validation only:** Doesn't prevent bugs, only detects them
❌ **Compile-time assertions:** Redundant with Rust's exhaustiveness checking

---

## Implementation Plan

### Phase 1: Immediate (This Week)
1. ✅ Audit: `grep -rn "_ =>" rust/compiler/src/codegen/{llvm,vulkan}/`
2. ✅ Remove catch-alls in LLVM backend
3. ✅ Remove catch-alls in Vulkan backend
4. ✅ Add lint: `#![deny(unreachable_patterns)]`
5. ✅ Verify: `cargo build --all-features`

### Phase 2: Short-Term (This Sprint)
1. ✅ Add instruction coverage tests
2. ✅ Add differential testing (Cranelift vs LLVM)
3. ✅ Integrate into CI pipeline

### Phase 3: Medium-Term (Next Month)
1. ✅ Create backend capability matrix
2. ✅ Auto-generate documentation
3. ✅ Track implementation progress

### Phase 4: Long-Term (When Needed)
1. ⏸️ Design DSL for instruction definitions (only if boilerplate becomes unmaintainable)

---

## Success Metrics

After Phase 1 & 2 implementation:
- ✅ Adding new MirInst variant **fails compilation** if any backend doesn't handle it
- ✅ All 80+ instructions tested in all 3 backends
- ✅ Zero runtime surprises from missing implementations
- ✅ Clear error messages: "GPU intrinsics not supported by LLVM backend"

---

## Quick Start Commands

```bash
# Find all dangerous catch-all patterns
grep -rn "_ =>" rust/compiler/src/codegen/{llvm,vulkan}/ | grep -v "test"

# Remove catch-alls and fix compilation
cargo build --all-features 2>&1 | grep "non-exhaustive"

# Run coverage tests (after implementing)
cargo test --test backend_coverage

# Generate backend documentation (after implementing)
cargo run --bin generate-backend-docs
```

---

## Key Takeaways

1. **Exhaustive pattern matching is the gold standard** - used by all major compilers
2. **Rust's compiler is our best tool** - leverage exhaustiveness checking
3. **Testing complements, doesn't replace** compile-time safety
4. **Start simple, automate later** - DSL is valuable but not urgent
5. **Zero catch-all patterns** - make missing implementations a compile error

**See full report for detailed research, implementation examples, and academic references.**
