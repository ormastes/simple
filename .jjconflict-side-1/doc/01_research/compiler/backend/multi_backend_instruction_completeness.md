# Multi-Backend Compiler Instruction Completeness: Research Report

**Date:** 2026-01-31
**Context:** Simple compiler with 80+ MIR instruction variants, multiple backends (Cranelift, LLVM, Vulkan)
**Problem:** Preventing missing instruction implementations across backends

## Executive Summary

This report analyzes best practices from major compilers (LLVM, Rust, GCC, WebAssembly) and academic research to prevent missing instruction lowering in multi-backend compilers. Based on this research and our codebase analysis, we recommend a **hybrid approach** combining compile-time exhaustiveness (primary), automated testing (safety net), and optional code generation for new backends.

**Key Finding:** Most production compilers rely on **exhaustive pattern matching** as the primary defense, backed by comprehensive testing. Code generation (TableGen, ISLE) is used to reduce boilerplate but doesn't replace exhaustiveness.

---

## 1. Research Findings from Major Compilers

### 1.1 Rust Compiler (Multiple Backends: LLVM, Cranelift, GCC)

**Architecture:**
- Backend-agnostic MIR shared across all backends via `rustc_codegen_ssa` crate
- Backend-specific implementations in separate crates (`rustc_codegen_llvm`, `rustc_codegen_cranelift`, `rustc_codegen_gcc`)
- Common trait interface for all backends

**Key Insights:**
- **Cranelift uses ISLE DSL** for instruction selection, which compiles to exhaustive Rust match expressions
- ISLE generates "a tree of match expressions as good as or better than what you would have written by hand" ([Cranelift's Instruction Selector DSL, ISLE](https://cfallin.org/blog/2023/01-20/cranelift-isle/))
- All Cranelift backends fully transitioned to ISLE, initially with fallback to handwritten code, then complete migration
- **Verification:** ISLE's declarative specification enables machine-checking of translations from IR to machine code ([Cranelift Progress in 2022](https://bytecodealliance.org/articles/cranelift-progress-2022))
- **Performance:** Generated code operates in a single pass, merging all rules into a decision tree

**Lessons for Simple:**
- DSL-based code generation is valuable but **outputs exhaustive pattern matching**
- Gradual migration strategy: fallback → incremental coverage → full exhaustiveness
- Type-safe DSL prevents many errors at the meta-compilation level

### 1.2 LLVM Project (50+ Target Architectures)

**Architecture:**
- TableGen DSL defines instructions, registers, and lowering rules in `.td` files
- Generates C++ code for instruction selection, code emission, and assembly printing
- Multiple backend verification passes

**Key Mechanisms:**

1. **TableGen Code Generation:**
   - Automates "massive amounts of information regarding instructions, schedules, cores, and architecture features" ([TableGen Overview](https://llvm.org/docs/TableGen/))
   - Tracks all classes (e.g., `Instruction`) so backends can ensure complete coverage
   - **Current limitation:** PseudoLoweringEmitter can only expand to single instructions ([TableGen pseudo lowering discussion](https://groups.google.com/g/llvm-dev/c/TcPWm4KUBL8/m/XloSBHPYCAAJ))

2. **Built-in Verifier Pass:**
   - Runs automatically after parsing and before optimizer output
   - Verifies IR well-formedness ([LLVM Language Reference](https://llvm.org/docs/LangRef.html))
   - "Violations pointed out by the verifier indicate bugs in transformation passes"

3. **Testing Strategy:**
   - FileCheck tool scans compiler output for expected patterns
   - Tests are "immune to irrelevant code generation changes like arbitrary register selection" ([Testing the MSVC Compiler Backend](https://devblogs.microsoft.com/cppblog/testing-the-msvc-compiler-backend/))
   - Heavy reliance on "real world code" (RWC): building Visual Studio, Windows, SQL, Office

**Lessons for Simple:**
- Code generation reduces boilerplate but doesn't guarantee completeness
- Runtime verification passes catch missing implementations at IR level
- Real-world application testing is crucial (in our case: stdlib, examples)

### 1.3 WebAssembly Compilers (Crocus for Cranelift)

**Crocus Verification Tool:**
- Lightweight verification for WebAssembly-to-native instruction selection in Cranelift
- Reasons about correctness in instruction lowering while trusting other compiler passes
- **Key finding:** "Instruction-lowering rules are error-prone even for experienced compiler engineers" ([Lightweight, Modular Verification for WebAssembly-to-Native Instruction Selection](https://cs.wellesley.edu/~avh/veri-isle-preprint.pdf))
- Issues involve "subtle interactions between constants, sign/zero-extensions, and tricky bitwidth-specific reasoning"

**VeriWasm Approach:**
- Verifies individual binaries (not the compiler)
- Proves they don't violate WebAssembly safety guarantees
- Compiler verification "provides strongest guarantees but is ambitious"

**Lessons for Simple:**
- Even with DSL-based code generation (ISLE), verification is needed
- Instruction lowering is inherently error-prone
- Per-binary verification is lighter-weight than full compiler verification

### 1.4 MLIR (Multi-Level IR)

**Dialect Conversion Framework:**
- Formal `ConversionTarget` defines what's legal during conversion
- **Full conversion:** All operations must be legalized (fails if any are missing)
- **Partial conversion:** Legalizes as many ops as possible, allows pre-existing legal ops
- Verifiers run between passes to ensure IR validity ([MLIR Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/))

**Recent Work on Verification Completeness:**
- "First-Class Verification Dialects for MLIR" introduces semantic dialects
- All operations can be expressed as lowerings to SMT dialect for complete semantics
- Most existing transformations "do not declare their pre/post-conditions explicitly" ([First-Class Verification Dialects for MLIR](https://users.cs.utah.edu/~regehr/papers/pldi25.pdf))

**Lessons for Simple:**
- Explicit legal/illegal operation declarations help detect missing lowerings
- Full conversion mode is safer than partial (all-or-nothing approach)
- Formal pre/post-conditions enable verification

### 1.5 GCC (Multiple Architectures)

**Architecture Support:**
- Target-specific subdirectories in `gcc/config` ([GCC Backends Status](https://gcc.gnu.org/backends.html))
- Function multi-versioning (FMV) for architecture-specific optimizations
- Gcov for code coverage analysis ([Gcov](https://gcc.gnu.org/onlinedocs/gcc/Gcov.html))

**Testing Strategy:**
- Instrumentation with `-fprofile-arcs` and `-ftest-coverage`
- Program flow graph analysis, spanning tree for minimal instrumentation
- Cross-architecture testing matrix

**Lessons for Simple:**
- Coverage instrumentation helps find untested code paths
- Architecture-specific testing matrices are essential

---

## 2. Academic Research on Compiler Correctness

### 2.1 Compiler Backend Verification

**CompCert (Xavier Leroy):**
- Formally verified compiler backend from Cminor to assembly
- Uses Coq proof assistant to prove correctness ([Formal Certification of a Compiler Back-end](https://xavierleroy.org/publi/compiler-certif.pdf))
- "Compiler backends are expected to produce correct code, but backends built on implicit models of hardware can have hard-to-find bugs"

**CakeML:**
- "Most realistic verified compiler for a functional language to date"
- 12 intermediate languages with formal semantics
- Proves compiler correctness end-to-end ([The verified CakeML compiler backend](https://www.semanticscholar.org/paper/The-verified-CakeML-compiler-backend-Tan-Myreen/fb7167c77866d866afba184261ffda028a00caf0))

**Key Insight:** Formal verification is the gold standard but extremely expensive. Most compilers use testing + partial verification instead.

### 2.2 Compiler Testing Techniques

**Empirical Comparison of Compiler Testing (ICSE 2016):**
- Main techniques: Randomized Differential Testing (RDT), Different Optimization Levels (DOL), Equivalence Modulo Inputs (EMI)
- DOL better for optimization bugs, RDT better for other bugs, **techniques complement each other**
- ([An empirical comparison of compiler testing techniques](https://dl.acm.org/doi/10.1145/2884781.2884878))

**SpecTest (Specification-Based Testing):**
- Uses executable semantics as test oracle
- Combines mutation testing and fuzzing to target less-tested language features
- Discovers "deep semantic errors" ([SpecTest: Specification-Based Compiler Testing](https://pmc.ncbi.nlm.nih.gov/articles/PMC7978860/))

**Testing New Compilers:**
- Grammar-based synthesis from code snippets when no reference compiler exists
- Metamorphic testing constructs equivalent programs under any inputs
- ([Testing the Compiler for a New-Born Programming Language](https://dl.acm.org/doi/10.1145/3597926.3598077))

**Lessons for Simple:**
- No single testing technique is sufficient
- Differential testing requires multiple backends or optimization levels
- Specification-based testing catches semantic errors

### 2.3 Backend Code Generation from Hardware Models

**Gus Henry Smith Dissertation:**
- "Generation of Compiler Backends from Formal Models of Hardware"
- Questions: "Does the target model formalize the previous version of the ISA?"
- "Does it formalize a restricted version of the source language?"
- ([Generation of Compiler Backends from Formal Models](https://digital.lib.washington.edu/researchworks/bitstreams/7081ea4a-ae6e-429a-86b1-0c5936138544/download))

**Key Insight:** Even generated backends need verification that the model is complete and accurate.

---

## 3. Current State of Simple Compiler

### 3.1 Architecture Analysis

**Codebase Structure:**
- **Single MIR:** 80+ instruction variants in `rust/compiler/src/mir/inst_enum.rs` (869 lines)
- **Backend Trait:** `NativeBackend` in `rust/compiler/src/codegen/backend_trait.rs`
- **Three Backends:**
  1. **Cranelift** (primary): Uses exhaustive pattern matching
  2. **LLVM** (secondary): Has catch-all patterns (`_ => {}`) in some places
  3. **Vulkan** (GPU): Has catch-all patterns in SPIR-V lowering

**Evidence of Catch-all Patterns:**

```bash
# LLVM backend (rust/compiler/src/codegen/llvm/instructions.rs)
67:     _ => return Err(crate::error::factory::unsupported_operation("integer binop", &op)),
85:     _ => return Err(crate::error::factory::unsupported_operation("float binop", &op)),
89:     _ => { /* type mismatch */ }

# Vulkan backend (rust/compiler/src/codegen/vulkan/spirv_instructions.rs)
154:    _ => { /* missing implementation */ }
408:    _ => { /* missing implementation */ }
```

**Current Backend Pattern:**
- Cranelift: ✅ Exhaustive matching (compile-time safe)
- LLVM: ⚠️ Partial catch-all patterns (some instructions return errors, some silent)
- Vulkan: ⚠️ Catch-all patterns (missing implementations)

### 3.2 Risk Assessment

**High Risk:**
- Silent failures in Vulkan backend (lines 154, 408)
- No automated detection when new MIR instructions are added
- Catch-all patterns hide missing implementations

**Medium Risk:**
- LLVM's `unsupported_operation` errors catch some cases at runtime
- But these are discovered only when the code path is executed

**Low Risk:**
- Cranelift backend is compile-time safe
- Rust's exhaustiveness checking prevents omissions

---

## 4. Recommended Approaches (Ranked)

### Approach 1: Exhaustive Pattern Matching (Primary Defense)

**Description:** Remove all catch-all patterns, force every backend to handle every instruction.

**Implementation:**
```rust
// Current (UNSAFE):
impl LlvmBackend {
    fn lower_instruction(&mut self, inst: &MirInst) -> Result<(), CompileError> {
        match inst {
            MirInst::ConstInt { .. } => { /* ... */ }
            MirInst::BinOp { .. } => { /* ... */ }
            _ => {} // DANGEROUS: silently ignores new instructions
        }
    }
}

// Recommended (SAFE):
impl LlvmBackend {
    fn lower_instruction(&mut self, inst: &MirInst) -> Result<(), CompileError> {
        match inst {
            MirInst::ConstInt { .. } => { /* ... */ }
            MirInst::BinOp { .. } => { /* ... */ }

            // Explicitly list unimplemented instructions
            MirInst::GpuGlobalId { .. } => {
                Err(CompileError::unsupported("LLVM backend doesn't support GPU intrinsics"))
            }
            MirInst::GpuBarrier => {
                Err(CompileError::unsupported("LLVM backend doesn't support GPU intrinsics"))
            }
            // ... all other variants must be listed
        }
        // No catch-all allowed!
    }
}
```

**Pros:**
- ✅ Compile-time safety: Rust compiler forces updates when MIR changes
- ✅ Zero runtime cost
- ✅ Self-documenting: every instruction is visible in the code
- ✅ Works with Rust's existing tooling (rustc, rust-analyzer)
- ✅ No additional dependencies or build steps

**Cons:**
- ❌ More verbose than catch-all patterns
- ❌ Requires discipline to maintain
- ❌ Each backend must explicitly handle every instruction (even if unsupported)

**Evidence from Research:**
- Rust/Cranelift: ISLE generates exhaustive matches ([ISLE: Term-Rewriting Made Practical](https://cfallin.org/blog/2023/01-20/cranelift-isle/))
- MLIR: Full conversion mode requires all ops legalized ([MLIR Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/))
- Best practice across all researched compilers

**Recommendation for Simple:** ✅ **PRIMARY APPROACH**
- Remove all `_ => {}` catch-alls in LLVM and Vulkan backends
- Replace with explicit error returns for unsupported instructions
- Enable `#[deny(unreachable_patterns)]` lint to catch redundant matches

### Approach 2: Trait-Based Required Methods (Secondary Defense)

**Description:** Split `NativeBackend::compile()` into required methods per instruction category.

**Implementation:**
```rust
// Current (single method):
pub trait NativeBackend {
    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>, CompileError>;
}

// Recommended (granular methods):
pub trait NativeBackend {
    // Constants
    fn lower_const_int(&mut self, dest: VReg, value: i64) -> Result<(), CompileError>;
    fn lower_const_float(&mut self, dest: VReg, value: f64) -> Result<(), CompileError>;

    // Operations
    fn lower_binop(&mut self, dest: VReg, op: BinOp, left: VReg, right: VReg)
        -> Result<(), CompileError>;

    // Memory
    fn lower_load(&mut self, dest: VReg, addr: VReg, ty: TypeId)
        -> Result<(), CompileError>;

    // GPU (optional with default error)
    fn lower_gpu_barrier(&mut self) -> Result<(), CompileError> {
        Err(CompileError::unsupported("GPU intrinsics not supported by this backend"))
    }

    // ... 80+ methods total
}
```

**Pros:**
- ✅ Compiler enforces implementation of required methods
- ✅ Clear interface documentation
- ✅ Allows default implementations for optional features
- ✅ Better IDE autocomplete

**Cons:**
- ❌ Very large trait (80+ methods for 80+ instructions)
- ❌ Tightly couples backend to MIR structure
- ❌ Adding new instructions requires trait changes (breaking change)
- ❌ Less flexible than pattern matching
- ❌ Doesn't compose well with instruction categories

**Evidence from Research:**
- Not commonly used in major compilers
- LLVM's `SelectionDAG` uses class hierarchies, not traits
- Rust's codegen uses shared functions, not required trait methods

**Recommendation for Simple:** ❌ **NOT RECOMMENDED**
- Too rigid for 80+ instructions
- Pattern matching is more idiomatic in Rust
- Breaks when MIR evolves

### Approach 3: Code Generation from Instruction Definitions (Build-Time Defense)

**Description:** Define instructions once, generate backend stubs automatically.

**Implementation:**
```rust
// Define instructions in a macro or external DSL:
define_mir_instructions! {
    ConstInt { dest: VReg, value: i64 },
    ConstFloat { dest: VReg, value: f64 },
    BinOp { dest: VReg, op: BinOp, left: VReg, right: VReg },
    // ... all 80+ instructions
}

// Macro generates:
// 1. MirInst enum
// 2. Backend trait with required methods
// 3. Exhaustive match stubs for each backend
// 4. Test harness to verify coverage
```

**Pros:**
- ✅ Single source of truth for instruction definitions
- ✅ Eliminates manual synchronization
- ✅ Can generate tests, documentation, etc.
- ✅ Easier to add new instructions

**Cons:**
- ❌ Adds complexity to build system
- ❌ Macro debugging is harder than regular code
- ❌ Generated code is less readable
- ❌ May not handle complex instruction-specific logic
- ❌ Requires custom tooling

**Evidence from Research:**
- LLVM TableGen: "keeps track of all classes so backends can ensure coverage" ([TableGen Overview](https://llvm.org/docs/TableGen/))
- Cranelift ISLE: compiles to exhaustive Rust matches ([Cranelift ISLE](https://cfallin.org/blog/2023/01-20/cranelift-isle/))
- Both still rely on developer discipline for complete implementations

**Recommendation for Simple:** ⏸️ **FUTURE ENHANCEMENT**
- Beneficial long-term but not urgent
- Start with Approach 1 (exhaustive matching)
- Consider DSL when:
  - We have 5+ backends
  - Instruction count exceeds 150+
  - Boilerplate becomes unmaintainable

### Approach 4: Automated Testing for Coverage (Runtime Safety Net)

**Description:** Write tests that verify each instruction is implemented in each backend.

**Implementation:**
```rust
#[cfg(test)]
mod backend_coverage_tests {
    use super::*;

    /// Generates test MIR for each instruction variant
    fn all_instructions() -> Vec<MirInst> {
        vec![
            MirInst::ConstInt { dest: VReg(0), value: 42 },
            MirInst::ConstFloat { dest: VReg(1), value: 3.14 },
            MirInst::BinOp {
                dest: VReg(2),
                op: BinOp::Add,
                left: VReg(0),
                right: VReg(1)
            },
            // ... all 80+ instructions
        ]
    }

    #[test]
    fn test_llvm_backend_handles_all_instructions() {
        let backend = LlvmBackend::new();
        for inst in all_instructions() {
            let result = backend.lower_instruction(&inst);
            // Should either succeed or return explicit unsupported error
            match result {
                Ok(_) => { /* good */ }
                Err(CompileError::Unsupported(_)) => { /* documented limitation */ }
                Err(e) => panic!("Unexpected error for {:?}: {:?}", inst, e),
            }
        }
    }

    #[test]
    fn test_vulkan_backend_handles_all_instructions() {
        // Same test for Vulkan backend
    }
}
```

**Enhanced: Differential Testing:**
```rust
#[test]
fn test_backend_consistency() {
    let test_program = /* simple MIR program */;

    let cranelift_result = compile_with_backend(BackendKind::Cranelift, &test_program);
    let llvm_result = compile_with_backend(BackendKind::Llvm, &test_program);

    // Results should be semantically equivalent
    assert_equivalent(cranelift_result, llvm_result);
}
```

**Pros:**
- ✅ Catches missing implementations at test time
- ✅ Validates semantic equivalence across backends
- ✅ Can be automated in CI/CD
- ✅ Complements compile-time checks
- ✅ Easy to add new test cases

**Cons:**
- ❌ Doesn't prevent bugs, only detects them
- ❌ Requires running tests to find issues
- ❌ Test coverage may have gaps
- ❌ More maintenance as instructions grow

**Evidence from Research:**
- MSVC: FileCheck + real-world code testing ([Testing the MSVC Compiler Backend](https://devblogs.microsoft.com/cppblog/testing-the-msvc-compiler-backend/))
- EMI, RDT, DOL: complementary testing techniques ([Empirical comparison of compiler testing](https://dl.acm.org/doi/10.1145/2884781.2884878))
- SpecTest: specification-based testing for deep errors ([SpecTest](https://pmc.ncbi.nlm.nih.gov/articles/PMC7978860/))

**Recommendation for Simple:** ✅ **SECONDARY APPROACH (COMPLEMENT TO APPROACH 1)**
- Add coverage tests for each backend
- Use differential testing across Cranelift/LLVM where both support an instruction
- Run tests in CI on every commit

### Approach 5: Compile-Time Assertions and Static Analysis (Build-Time Safety)

**Description:** Use Rust's type system and build-time checks to enforce completeness.

**Implementation:**
```rust
// Use const assertions to verify instruction count matches backend implementations
const _: () = {
    const INSTRUCTION_COUNT: usize = std::mem::variant_count::<MirInst>();
    const LLVM_IMPLEMENTED: usize = 65; // Update when adding implementations

    if LLVM_IMPLEMENTED < INSTRUCTION_COUNT {
        panic!("LLVM backend is missing implementations!");
    }
};

// Or use procedural macro to count match arms:
#[derive(EnforceExhaustive)]
impl LlvmBackend {
    #[exhaustive_match(MirInst)] // Proc macro verifies all variants handled
    fn lower_instruction(&mut self, inst: &MirInst) -> Result<(), CompileError> {
        match inst {
            // ...
        }
    }
}
```

**Pros:**
- ✅ Compile-time enforcement
- ✅ Automated, no manual checks needed
- ✅ Clear error messages

**Cons:**
- ❌ Requires procedural macros or const eval
- ❌ More complex than pattern matching
- ❌ May not work well with Rust's exhaustiveness checker

**Evidence from Research:**
- Not commonly used in major compilers
- Rust's built-in exhaustiveness is usually sufficient

**Recommendation for Simple:** ❌ **NOT NEEDED**
- Rust's exhaustiveness checking already provides this
- Approach 1 (removing catch-alls) is simpler and equally effective

### Approach 6: Runtime Validation Pass (Runtime Safety Net)

**Description:** Add a verification pass that checks MIR can be lowered before attempting codegen.

**Implementation:**
```rust
pub trait NativeBackend {
    /// Check if this backend supports the given MIR module
    /// Returns list of unsupported instructions
    fn validate_support(&self, module: &MirModule) -> Vec<UnsupportedInst>;

    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>, CompileError> {
        // Pre-flight check
        let unsupported = self.validate_support(module);
        if !unsupported.is_empty() {
            return Err(CompileError::UnsupportedInstructions(unsupported));
        }

        // Actual compilation
        self.compile_impl(module)
    }
}
```

**Pros:**
- ✅ Clear error messages before compilation starts
- ✅ Can list all unsupported features at once
- ✅ User-friendly error reporting

**Cons:**
- ❌ Adds runtime overhead
- ❌ Duplicates logic (validation + implementation)
- ❌ Can become out of sync

**Evidence from Research:**
- LLVM verifier: runs after parsing and before optimizer ([LLVM Language Reference](https://llvm.org/docs/LangRef.html))
- MLIR: verifiers run between passes ([MLIR Testing Guide](https://mlir.llvm.org/getting_started/TestingGuide/))

**Recommendation for Simple:** ⏸️ **OPTIONAL ENHANCEMENT**
- Useful for better error messages
- Not a substitute for Approach 1
- Consider adding after exhaustive matching is enforced

---

## 5. Recommended Implementation Plan for Simple

### Phase 1: Immediate (Compile-Time Safety)
**Goal:** Make missing implementations a compile error.

**Actions:**
1. **Audit current backends:**
   ```bash
   # Find all catch-all patterns
   grep -rn "_ =>" rust/compiler/src/codegen/{llvm,vulkan}/ \
       | grep -v "test" > catchalls.txt
   ```

2. **Remove catch-alls in LLVM backend:**
   - Replace `_ => {}` with explicit instruction matches
   - Return `Err(CompileError::unsupported("..."))` for unimplemented features
   - Example: `MirInst::GpuBarrier => Err(...)`

3. **Remove catch-alls in Vulkan backend:**
   - Same process as LLVM
   - Vulkan should only handle GPU-specific instructions, return error for others

4. **Add lint configuration:**
   ```rust
   #![deny(unreachable_patterns)]
   #![warn(clippy::wildcard_enum_match_arm)]
   ```

5. **Verify compilation:**
   ```bash
   cargo build --all-features 2>&1 | tee build.log
   ```

**Expected Result:**
- Adding new `MirInst` variant will break compilation if any backend doesn't handle it
- Clear error messages: "non-exhaustive patterns: `MirInst::NewInstruction` not covered"

### Phase 2: Short-Term (Testing Safety Net)
**Goal:** Catch missing implementations and semantic bugs.

**Actions:**
1. **Add instruction coverage tests:**
   ```rust
   // In rust/compiler/src/codegen/tests/coverage.rs
   #[test]
   fn test_llvm_instruction_coverage() {
       let backend = LlvmBackend::new();
       for inst in MirInst::all_variants() {
           let result = backend.lower_instruction(&inst);
           // Either succeeds or explicitly unsupported
           assert!(result.is_ok() || matches!(result, Err(CompileError::Unsupported(_))));
       }
   }
   ```

2. **Add differential testing:**
   ```rust
   #[test]
   fn test_backend_equivalence() {
       let test_cases = generate_mir_test_programs();
       for program in test_cases {
           let cranelift = compile_and_run(BackendKind::Cranelift, &program);
           let llvm = compile_and_run(BackendKind::Llvm, &program);
           assert_semantically_equivalent(cranelift, llvm);
       }
   }
   ```

3. **Add to CI pipeline:**
   ```yaml
   # .github/workflows/ci.yml
   - name: Backend Coverage Tests
     run: cargo test --test backend_coverage
   ```

**Expected Result:**
- Tests fail if any backend silently ignores an instruction
- Differential tests catch semantic differences between backends

### Phase 3: Medium-Term (Documentation and Tracking)
**Goal:** Make backend capabilities explicit and trackable.

**Actions:**
1. **Create backend capability matrix:**
   ```rust
   // In rust/compiler/src/codegen/capabilities.rs
   pub struct BackendCapabilities {
       pub supports_gpu: bool,
       pub supports_simd: bool,
       pub supports_32bit: bool,
       pub max_instruction_set: InstructionSet,
   }

   impl LlvmBackend {
       pub fn capabilities() -> BackendCapabilities {
           BackendCapabilities {
               supports_gpu: false,
               supports_simd: true,
               supports_32bit: true,
               max_instruction_set: InstructionSet::Full,
           }
       }
   }
   ```

2. **Generate documentation:**
   ```bash
   # Auto-generate doc/backend_support.md
   cargo run --bin generate-backend-docs
   ```

3. **Track implementation progress:**
   ```markdown
   # Backend Implementation Status

   | Instruction | Cranelift | LLVM | Vulkan |
   |-------------|-----------|------|--------|
   | ConstInt    | ✅        | ✅   | ✅     |
   | GpuBarrier  | ❌        | ❌   | ✅     |
   | ...         | ...       | ...  | ...    |
   ```

**Expected Result:**
- Clear visibility into what each backend supports
- Documentation stays in sync with code

### Phase 4: Long-Term (Optional Code Generation)
**Goal:** Reduce boilerplate as instruction count grows.

**Actions:**
1. **Design Simple DSL (or use existing macro):**
   ```rust
   mir_instructions! {
       category "Constants" {
           ConstInt { dest: VReg, value: i64 } => "Load constant integer",
           ConstFloat { dest: VReg, value: f64 } => "Load constant float",
       }
       category "GPU" {
           GpuBarrier => "GPU memory barrier",
           GpuGlobalId { dest: VReg, dim: u32 } => "Get GPU global ID",
       }
   }
   ```

2. **Generate enum + backend stubs:**
   - MirInst enum definition
   - Match arm templates for each backend
   - Test harness

3. **Migration strategy:**
   - Keep existing code initially
   - Gradually migrate to generated code
   - Verify equivalence at each step

**Expected Result:**
- Adding new instruction updates all backends automatically
- Less manual synchronization

---

## 6. Comparison Table

| Approach | Compile-Time Safety | Runtime Cost | Implementation Effort | Maintainability | Recommended |
|----------|--------------------:|-------------:|----------------------:|----------------:|------------:|
| **1. Exhaustive Matching** | ✅✅✅ High | ✅ Zero | ⭐⭐ Medium | ⭐⭐⭐ High | ✅ **PRIMARY** |
| **2. Trait Methods** | ✅✅ Medium | ✅ Zero | ⭐⭐⭐ High | ⭐ Low | ❌ No |
| **3. Code Generation** | ✅✅✅ High | ✅ Zero | ⭐⭐⭐⭐ Very High | ⭐⭐⭐⭐ Very High | ⏸️ Future |
| **4. Automated Testing** | ❌ None | ❌ Test-time only | ⭐⭐ Medium | ⭐⭐⭐ High | ✅ **SECONDARY** |
| **5. Compile-Time Assertions** | ✅✅ Medium | ✅ Zero | ⭐⭐⭐ High | ⭐⭐ Medium | ❌ Redundant |
| **6. Runtime Validation** | ❌ None | ❌ Runtime overhead | ⭐⭐ Medium | ⭐⭐ Medium | ⏸️ Optional |

---

## 7. Conclusion

### Primary Recommendation: Hybrid Approach

**Tier 1 (Must Have):**
1. **Exhaustive pattern matching** in all backends (Approach 1)
   - Remove all `_ => {}` catch-alls
   - Force explicit handling of every instruction
   - Enable exhaustiveness lints

2. **Automated coverage tests** (Approach 4)
   - Per-backend instruction coverage
   - Differential testing across backends
   - CI integration

**Tier 2 (Should Have):**
3. **Backend capability tracking** (Phase 3 of implementation plan)
   - Document what each backend supports
   - Clear error messages for unsupported features

**Tier 3 (Nice to Have):**
4. **Code generation from DSL** (Approach 3)
   - When instruction count exceeds 150+
   - When we have 5+ backends
   - When boilerplate becomes unmaintainable

### Why This Works for Simple

1. **Current scale is manageable:**
   - 80 instructions, 3 backends = ~240 match arms
   - Exhaustive matching is practical at this scale
   - Rust's compiler provides excellent support

2. **Aligns with research findings:**
   - Cranelift/ISLE, LLVM/TableGen both generate exhaustive matches
   - Testing is universal across all major compilers
   - Formal verification is overkill for our needs

3. **Incremental adoption:**
   - Phase 1 (exhaustive matching) is low-risk
   - Phase 2 (testing) complements existing test suite
   - Phase 3-4 can be deferred

4. **Leverages Rust's strengths:**
   - Pattern matching is idiomatic
   - Compiler catches missing arms automatically
   - No runtime cost

### Key Metrics to Track

After implementing recommendations, measure:
- ✅ Compilation fails when new instruction added but not implemented
- ✅ Test coverage: all instructions tested in all backends
- ✅ Time to add new instruction: should decrease with automation
- ✅ Bug rate: missing instruction implementations should be zero

---

## 8. Sources

### Major Compilers
- [Rust Compiler Codegen](https://rustc-dev-guide.rust-lang.org/backend/codegen.html)
- [Cranelift's Instruction Selector DSL, ISLE](https://cfallin.org/blog/2023/01-20/cranelift-isle/)
- [Cranelift Progress in 2022](https://bytecodealliance.org/articles/cranelift-progress-2022)
- [LLVM TableGen Overview](https://llvm.org/docs/TableGen/)
- [LLVM Language Reference](https://llvm.org/docs/LangRef.html)
- [Testing the MSVC Compiler Backend](https://devblogs.microsoft.com/cppblog/testing-the-msvc-compiler-backend/)
- [MLIR Dialect Conversion](https://mlir.llvm.org/docs/DialectConversion/)
- [GCC Backends Status](https://gcc.gnu.org/backends.html)

### Academic Research
- [Formal Certification of a Compiler Back-end (Xavier Leroy)](https://xavierleroy.org/publi/compiler-certif.pdf)
- [The verified CakeML compiler backend](https://www.semanticscholar.org/paper/The-verified-CakeML-compiler-backend-Tan-Myreen/fb7167c77866d866afba184261ffda028a00caf0)
- [An empirical comparison of compiler testing techniques (ICSE 2016)](https://dl.acm.org/doi/10.1145/2884781.2884878)
- [SpecTest: Specification-Based Compiler Testing](https://pmc.ncbi.nlm.nih.gov/articles/PMC7978860/)
- [Testing the Compiler for a New-Born Programming Language (ISSTA 2023)](https://dl.acm.org/doi/10.1145/3597926.3598077)
- [Generation of Compiler Backends from Formal Models (Gus Henry Smith)](https://digital.lib.washington.edu/researchworks/bitstreams/7081ea4a-ae6e-429a-86b1-0c5936138544/download)
- [First-Class Verification Dialects for MLIR](https://users.cs.utah.edu/~regehr/papers/pldi25.pdf)

### WebAssembly and Verification
- [Lightweight, Modular Verification for WebAssembly-to-Native Instruction Selection](https://cs.wellesley.edu/~avh/veri-isle-preprint.pdf)
- [WebAssembly Validation](https://webassembly.org/docs/security/)

---

**Next Steps:**
1. Review this report with the team
2. Get approval for Phase 1 (exhaustive matching)
3. Create tracking issues for each phase
4. Begin implementation following the phased plan
