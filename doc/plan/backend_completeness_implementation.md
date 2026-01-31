# Backend Instruction Completeness - Implementation Checklist

**Research Report:** `doc/research/multi_backend_instruction_completeness.md`
**Quick Summary:** `doc/research/backend_completeness_summary.md`
**Status:** Planning
**Created:** 2026-01-31

---

## Phase 1: Immediate Actions (Compile-Time Safety)

**Goal:** Make missing instruction implementations a compile error.
**Timeline:** Complete this week
**Blocking:** None

### Tasks

- [ ] **Task 1.1:** Audit current catch-all patterns
  ```bash
  grep -rn "_ =>" rust/compiler/src/codegen/{llvm,vulkan}/ \
      | grep -v "test" > doc/plan/catchall_audit.txt
  ```
  **Expected:** ~5-10 locations in LLVM backend, ~2-5 in Vulkan backend
  **Assignee:** TBD
  **Estimate:** 30 minutes

- [ ] **Task 1.2:** Remove catch-alls in LLVM backend
  - File: `rust/compiler/src/codegen/llvm/instructions.rs`
  - File: `rust/compiler/src/codegen/llvm/emitter.rs`
  - Replace `_ => {}` with explicit instruction matches
  - Return `Err(CompileError::unsupported("..."))` for unimplemented features
  **Assignee:** TBD
  **Estimate:** 4 hours

- [ ] **Task 1.3:** Remove catch-alls in Vulkan backend
  - File: `rust/compiler/src/codegen/vulkan/spirv_instructions.rs`
  - File: `rust/compiler/src/codegen/vulkan/emitter.rs`
  - Same process as LLVM
  - Vulkan should error for non-GPU instructions
  **Assignee:** TBD
  **Estimate:** 2 hours

- [ ] **Task 1.4:** Add exhaustiveness lints
  - Add to `rust/compiler/src/codegen/llvm/mod.rs`:
    ```rust
    #![deny(unreachable_patterns)]
    #![warn(clippy::wildcard_enum_match_arm)]
    ```
  - Add to `rust/compiler/src/codegen/vulkan/mod.rs`: (same)
  **Assignee:** TBD
  **Estimate:** 10 minutes

- [ ] **Task 1.5:** Verify compilation
  ```bash
  cargo build --all-features 2>&1 | tee doc/plan/phase1_build.log
  cargo clippy --all-features 2>&1 | grep "wildcard_enum" | tee doc/plan/phase1_clippy.log
  ```
  **Expected:** No warnings about wildcard patterns
  **Assignee:** TBD
  **Estimate:** 30 minutes

- [ ] **Task 1.6:** Test with new instruction addition
  - Add a dummy `MirInst::TestDummy` variant
  - Verify compilation fails with clear errors
  - Remove dummy variant
  **Assignee:** TBD
  **Estimate:** 30 minutes

**Total Estimate:** ~8 hours
**Success Criteria:**
- ✅ Zero `_ => {}` patterns in backend instruction lowering
- ✅ Adding new MirInst variant breaks compilation
- ✅ Clear error messages point to exact match expressions that need updates

---

## Phase 2: Short-Term (Testing Safety Net)

**Goal:** Catch missing implementations and semantic bugs.
**Timeline:** Complete this sprint (2 weeks)
**Blocking:** Phase 1 must be complete

### Tasks

- [ ] **Task 2.1:** Design test infrastructure
  - Create `rust/compiler/src/codegen/tests/coverage.rs`
  - Define `MirInst::all_test_variants()` helper
  - Design test case generator
  **Assignee:** TBD
  **Estimate:** 2 hours

- [ ] **Task 2.2:** Implement LLVM coverage test
  ```rust
  #[test]
  fn test_llvm_instruction_coverage() {
      let backend = LlvmBackend::new();
      for inst in MirInst::all_test_variants() {
          let result = backend.lower_instruction(&inst);
          assert!(
              result.is_ok() || matches!(result, Err(CompileError::Unsupported(_))),
              "Unexpected error for {:?}: {:?}", inst, result
          );
      }
  }
  ```
  **Assignee:** TBD
  **Estimate:** 3 hours

- [ ] **Task 2.3:** Implement Vulkan coverage test
  - Same structure as LLVM test
  - Verify GPU instructions succeed, others return unsupported
  **Assignee:** TBD
  **Estimate:** 1 hour

- [ ] **Task 2.4:** Implement Cranelift coverage test
  - Should pass for all instructions (reference implementation)
  **Assignee:** TBD
  **Estimate:** 1 hour

- [ ] **Task 2.5:** Add differential testing framework
  ```rust
  #[test]
  fn test_backend_equivalence_simple_program() {
      let program = generate_simple_mir();
      let cranelift_result = compile_with_backend(BackendKind::Cranelift, &program);
      let llvm_result = compile_with_backend(BackendKind::Llvm, &program);
      assert_semantically_equivalent(cranelift_result, llvm_result);
  }
  ```
  **Assignee:** TBD
  **Estimate:** 4 hours

- [ ] **Task 2.6:** Create test cases for each instruction category
  - Constants: ConstInt, ConstFloat, ConstBool
  - Arithmetic: BinOp (Add, Sub, Mul, Div)
  - Memory: Load, Store
  - Control flow: Branch, Call
  - GPU: GpuBarrier, GpuGlobalId
  **Assignee:** TBD
  **Estimate:** 6 hours

- [ ] **Task 2.7:** Integrate into CI pipeline
  - Add to `.github/workflows/ci.yml`:
    ```yaml
    - name: Backend Coverage Tests
      run: cargo test --test backend_coverage --all-features
    ```
  **Assignee:** TBD
  **Estimate:** 30 minutes

- [ ] **Task 2.8:** Document testing strategy
  - Add to `doc/test/backend_testing.md`
  - Explain coverage tests, differential tests
  - How to add new test cases
  **Assignee:** TBD
  **Estimate:** 1 hour

**Total Estimate:** ~19 hours
**Success Criteria:**
- ✅ All 80+ instructions tested in all backends
- ✅ Differential tests pass for Cranelift vs LLVM
- ✅ CI fails if any backend has missing implementation
- ✅ Clear documentation for future contributors

---

## Phase 3: Medium-Term (Documentation and Tracking)

**Goal:** Make backend capabilities explicit and trackable.
**Timeline:** Complete next month
**Blocking:** Phase 2 must be complete

### Tasks

- [ ] **Task 3.1:** Design capability matrix data structure
  ```rust
  pub struct BackendCapabilities {
      pub supports_gpu: bool,
      pub supports_simd: bool,
      pub supports_32bit: bool,
      pub instruction_support: HashMap<&'static str, bool>,
  }
  ```
  **Assignee:** TBD
  **Estimate:** 2 hours

- [ ] **Task 3.2:** Implement capability query for each backend
  ```rust
  impl LlvmBackend {
      pub fn capabilities() -> BackendCapabilities { /* ... */ }
  }
  impl VulkanBackend {
      pub fn capabilities() -> BackendCapabilities { /* ... */ }
  }
  ```
  **Assignee:** TBD
  **Estimate:** 3 hours

- [ ] **Task 3.3:** Create documentation generator
  - Script: `scripts/generate_backend_docs.rs`
  - Input: Backend capability queries + test results
  - Output: `doc/backend_support.md`
  **Assignee:** TBD
  **Estimate:** 4 hours

- [ ] **Task 3.4:** Generate backend support matrix
  ```markdown
  | Instruction | Cranelift | LLVM | Vulkan | Notes |
  |-------------|-----------|------|--------|-------|
  | ConstInt    | ✅        | ✅   | ✅     | |
  | GpuBarrier  | ❌        | ❌   | ✅     | GPU-only |
  ```
  **Assignee:** TBD
  **Estimate:** 2 hours

- [ ] **Task 3.5:** Add to build process
  ```bash
  # In Makefile
  docs: backend-docs

  backend-docs:
      cargo run --bin generate-backend-docs
  ```
  **Assignee:** TBD
  **Estimate:** 30 minutes

- [ ] **Task 3.6:** Document unsupported feature workflow
  - How to add new instruction
  - How to mark as unsupported in specific backend
  - Error message best practices
  **Assignee:** TBD
  **Estimate:** 2 hours

**Total Estimate:** ~14 hours
**Success Criteria:**
- ✅ Clear documentation of what each backend supports
- ✅ Auto-generated, stays in sync with code
- ✅ Easy to update when adding new instructions

---

## Phase 4: Long-Term (Code Generation - Optional)

**Goal:** Reduce boilerplate via DSL (only when needed).
**Timeline:** TBD (deferred until instruction count exceeds 150+)
**Blocking:** None (independent enhancement)

### Decision Criteria

Implement this phase when **any two** of:
- Instruction count exceeds 150 variants
- We have 5+ active backends
- Time to add new instruction exceeds 2 hours
- Boilerplate complaints from 3+ contributors

### Tasks (Tentative)

- [ ] **Task 4.1:** Research DSL options
  - Study LLVM TableGen implementation
  - Study Cranelift ISLE implementation
  - Evaluate Rust macro approaches
  **Estimate:** 8 hours

- [ ] **Task 4.2:** Design Simple IR DSL
  - Syntax for instruction definitions
  - Backend-specific lowering rules
  - Error handling patterns
  **Estimate:** 16 hours

- [ ] **Task 4.3:** Implement code generator
  - Parse DSL → AST
  - Generate Rust code (enum + match arms)
  - Generate tests
  **Estimate:** 40 hours

- [ ] **Task 4.4:** Migrate existing instructions
  - Convert MirInst enum to DSL
  - Verify generated code matches existing
  - Gradual rollout
  **Estimate:** 24 hours

**Total Estimate:** ~88 hours (11 days)
**Success Criteria:**
- ✅ DSL is easier to maintain than manual code
- ✅ Generated code quality matches handwritten
- ✅ Time to add new instruction reduces by 50%

**Note:** This phase is explicitly deferred. Current scale doesn't justify the investment.

---

## Risk Assessment

### Phase 1 Risks

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Breaking existing functionality | Medium | High | Comprehensive testing before/after |
| Missing edge cases | Medium | Medium | Code review + CI tests |
| Time estimate too low | Low | Low | Phase is straightforward |

### Phase 2 Risks

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Test coverage gaps | Medium | Medium | Systematic test case generation |
| False positives in differential tests | Medium | Low | Careful semantic equivalence definition |
| CI pipeline complexity | Low | Low | Standard Cargo test integration |

### Phase 3 Risks

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Documentation becomes stale | Medium | Low | Auto-generate from code |
| Overhead in maintenance | Low | Low | Minimal - runs once per release |

---

## Success Metrics (Overall)

### Quantitative

- **Compile-time errors:** 100% of missing implementations caught at compile time
- **Test coverage:** All 80+ instructions tested in all 3 backends
- **CI failure rate:** Zero false negatives (missing implementations always fail CI)
- **Time to add instruction:** Remains under 30 minutes (with exhaustive matching)

### Qualitative

- **Developer confidence:** No fear of silent failures
- **Code maintainability:** Clear which backends support which features
- **Error messages:** Users see helpful "unsupported feature" messages, not crashes

---

## Next Steps

1. **Review this plan** with team (estimated 1 hour meeting)
2. **Assign owners** for Phase 1 tasks
3. **Create tracking issues** in issue tracker
4. **Schedule Phase 1** for this week
5. **Begin implementation** following this checklist

---

## Updates Log

| Date | Phase | Status | Notes |
|------|-------|--------|-------|
| 2026-01-31 | Planning | Complete | Initial plan created |
| TBD | Phase 1 | Not started | Awaiting review |
| TBD | Phase 2 | Not started | Blocked by Phase 1 |
| TBD | Phase 3 | Not started | Blocked by Phase 2 |
| N/A | Phase 4 | Deferred | Only when scale justifies |
