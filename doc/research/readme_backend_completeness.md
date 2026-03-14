# Backend Instruction Completeness Research - Index

**Date:** 2026-01-31
**Research Question:** How do we prevent missing instruction implementations across multiple compiler backends?

---

## Quick Navigation

| Document | Purpose | Audience | Reading Time |
|----------|---------|----------|--------------|
| **[Summary](./backend_completeness_summary.md)** | Executive overview + quick start | Everyone | 5 min |
| **[Full Report](./multi_backend_instruction_completeness.md)** | Detailed research + recommendations | Technical leads | 30 min |
| **[Implementation Plan](../plan/backend_completeness_implementation.md)** | Phased implementation checklist | Implementers | 15 min |

---

## Research Deliverables

### 1. Quick Summary (5 min read)
**File:** `doc/research/backend_completeness_summary.md` (201 lines, 5.9KB)

**Contents:**
- TL;DR: Use exhaustive pattern matching + automated testing
- Current issues in Simple compiler (catch-all patterns)
- Recommended solution (2 tiers)
- Evidence from major compilers
- Quick start commands

**Read this if:** You need the answer quickly or want to brief others.

### 2. Full Research Report (30 min read)
**File:** `doc/research/multi_backend_instruction_completeness.md` (818 lines, 32KB)

**Contents:**
- Research from 6 major compiler projects (Rust, LLVM, GCC, WebAssembly, MLIR)
- Academic papers on compiler correctness (CompCert, CakeML, SpecTest)
- Current state analysis of Simple compiler (80+ instructions, 3 backends)
- 6 approaches evaluated with pros/cons
- Detailed implementation plan (4 phases)
- 30+ cited sources with links

**Read this if:** You need to understand the rationale, want academic backing, or are designing similar systems.

### 3. Implementation Checklist (15 min read)
**File:** `doc/plan/backend_completeness_implementation.md` (354 lines, 11KB)

**Contents:**
- 4 phased implementation plan with tasks, estimates, assignees
- Phase 1 (Immediate): Remove catch-all patterns - 8 hours
- Phase 2 (Short-term): Add coverage tests - 19 hours
- Phase 3 (Medium-term): Documentation - 14 hours
- Phase 4 (Long-term): Code generation DSL - 88 hours (deferred)
- Risk assessment + success metrics

**Read this if:** You're implementing the recommendations or tracking progress.

---

## Key Findings Summary

### The Problem
- Simple compiler has 80+ MIR instruction variants
- 3 backends: Cranelift (exhaustive), LLVM (partial catch-alls), Vulkan (catch-alls)
- Catch-all patterns (`_ => {}`) hide missing implementations
- Adding new instructions silently fails in secondary backends

### The Solution (Hybrid Approach)

**Tier 1 (Must Have):**
1. **Exhaustive pattern matching** - Force every backend to handle every instruction
2. **Automated testing** - Coverage tests + differential testing

**Why this works:**
- Cranelift/Rust: ISLE DSL generates exhaustive matches
- LLVM: TableGen + verifier passes
- All major compilers use this pattern

**Not recommended:**
- ❌ Large trait with 80+ required methods (too rigid)
- ❌ Runtime validation only (doesn't prevent bugs)
- ⏸️ Code generation DSL (beneficial but not urgent at current scale)

### Implementation Timeline

| Phase | Timeline | Effort | Status |
|-------|----------|--------|--------|
| Phase 1: Exhaustive matching | This week | 8 hours | Not started |
| Phase 2: Testing | This sprint (2 weeks) | 19 hours | Not started |
| Phase 3: Documentation | Next month | 14 hours | Not started |
| Phase 4: Code generation | Deferred | 88 hours | Only when scale justifies |

---

## Evidence from Major Compilers

### Rust Compiler + Cranelift
- **ISLE DSL** compiles to exhaustive Rust match expressions
- "As good as or better than handwritten code"
- Machine-checkable verification of IR → machine code translations
- **Source:** [Cranelift's Instruction Selector DSL, ISLE](https://cfallin.org/blog/2023/01-20/cranelift-isle/)

### LLVM
- **TableGen** automates instruction definition boilerplate
- **Built-in verifier** runs after every transformation
- Testing: FileCheck + real-world applications (Visual Studio, Windows, SQL)
- **Source:** [LLVM TableGen Overview](https://llvm.org/docs/TableGen/)

### WebAssembly (Crocus)
- Verification for Cranelift's instruction lowering
- Finding: "Instruction lowering is error-prone even for experienced engineers"
- Issues: "Subtle interactions between constants, sign/zero-extensions, bitwidth reasoning"
- **Source:** [Lightweight, Modular Verification for WebAssembly](https://cs.wellesley.edu/~avh/veri-isle-preprint.pdf)

### MLIR
- **Full conversion mode:** All operations must be legalized (fails if any missing)
- Verifiers run between passes
- Recent work on semantic dialects for completeness guarantees
- **Source:** [MLIR Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/)

---

## Quick Start (For Implementers)

### Step 1: Audit Current State (30 min)
```bash
# Find all catch-all patterns
grep -rn "_ =>" rust/compiler/src/codegen/{llvm,vulkan}/ \
    | grep -v "test" > catchalls.txt

# Count MIR instruction variants
grep -c "pub enum MirInst" rust/compiler/src/mir/inst_enum.rs

# Current: 80+ variants, ~5-10 catch-alls found
```

### Step 2: Remove Catch-Alls (4-6 hours)
```rust
// Before (UNSAFE):
match inst {
    MirInst::ConstInt { .. } => { /* ... */ }
    _ => {} // DANGEROUS
}

// After (SAFE):
match inst {
    MirInst::ConstInt { .. } => { /* ... */ }
    MirInst::GpuBarrier => Err(CompileError::unsupported("GPU not supported")),
    // ... all 80+ variants explicitly listed
}
```

### Step 3: Add Coverage Tests (3-4 hours)
```rust
#[test]
fn test_llvm_coverage() {
    for inst in MirInst::all_test_variants() {
        let result = backend.lower_instruction(&inst);
        assert!(result.is_ok() || matches!(result, Err(CompileError::Unsupported(_))));
    }
}
```

### Step 4: Integrate into CI (30 min)
```yaml
# .github/workflows/ci.yml
- name: Backend Coverage Tests
  run: cargo test --test backend_coverage --all-features
```

---

## Success Metrics

After Phase 1 & 2 implementation:

### Compile-Time
- ✅ Adding new `MirInst` variant fails compilation with clear error
- ✅ Error points to exact match expressions needing updates

### Runtime
- ✅ All 80+ instructions tested in all 3 backends
- ✅ Zero silent failures
- ✅ Clear "unsupported feature" errors instead of crashes

### Developer Experience
- ✅ Confidence: No fear of missing implementations
- ✅ Maintainability: Easy to see what each backend supports
- ✅ Time to add instruction: Under 30 minutes

---

## Related Documentation

### Existing
- `rust/compiler/src/mir/inst_enum.rs` - MIR instruction definitions (869 lines)
- `rust/compiler/src/codegen/backend_trait.rs` - NativeBackend trait
- `rust/compiler/src/codegen/cranelift.rs` - Reference implementation (exhaustive)
- `rust/compiler/src/codegen/llvm/instructions.rs` - LLVM backend (has catch-alls)
- `rust/compiler/src/codegen/vulkan/spirv_instructions.rs` - Vulkan backend (has catch-alls)

### To Be Created (Phase 2-3)
- `rust/compiler/src/codegen/tests/coverage.rs` - Coverage tests
- `doc/test/backend_testing.md` - Testing strategy documentation
- `doc/backend_support.md` - Auto-generated capability matrix
- `scripts/generate_backend_docs.rs` - Documentation generator

---

## Academic References

### Formal Verification
- **CompCert:** Formally verified compiler backend (Coq proofs)
  - [Formal Certification of a Compiler Back-end (Xavier Leroy)](https://xavierleroy.org/publi/compiler-certif.pdf)
- **CakeML:** Verified compiler with 12 intermediate languages
  - [The verified CakeML compiler backend](https://www.semanticscholar.org/paper/The-verified-CakeML-compiler-backend-Tan-Myreen/fb7167c77866d866afba184261ffda028a00caf0)

### Testing Strategies
- **Compiler Testing Techniques:** RDT, DOL, EMI comparison
  - [An empirical comparison (ICSE 2016)](https://dl.acm.org/doi/10.1145/2884781.2884878)
- **SpecTest:** Specification-based testing for semantic errors
  - [SpecTest paper](https://pmc.ncbi.nlm.nih.gov/articles/PMC7978860/)
- **Testing New Compilers:** Grammar-based + metamorphic testing
  - [New-Born Programming Language (ISSTA 2023)](https://dl.acm.org/doi/10.1145/3597926.3598077)

### Backend Generation
- **Hardware Models:** Generation from formal specifications
  - [Generation of Compiler Backends (Gus Henry Smith)](https://digital.lib.washington.edu/researchworks/bitstreams/7081ea4a-ae6e-429a-86b1-0c5936138544/download)

---

## Contact / Questions

**Research conducted by:** Claude Code (2026-01-31)
**Reviewed by:** TBD
**Implementation owner:** TBD

**For questions:**
- Technical approach: See full report Section 4 (Recommended Approaches)
- Implementation details: See implementation plan Phase 1-3 tasks
- Academic citations: See full report Section 8 (Sources)

---

## Version History

| Version | Date | Changes | Author |
|---------|------|---------|--------|
| 1.0 | 2026-01-31 | Initial research and recommendations | Claude Code |
| TBD | TBD | Phase 1 implementation completed | TBD |
| TBD | TBD | Phase 2 implementation completed | TBD |
| TBD | TBD | Phase 3 implementation completed | TBD |
