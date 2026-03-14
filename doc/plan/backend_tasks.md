# Backend Completeness - Task Tracker

**Date:** 2026-01-31
**Status:** Planning → Implementation
**Quick Start:** `doc/plan/BACKEND_COMPLETENESS_QUICKSTART.md`
**Full Plan:** `doc/plan/backend_completeness_full_implementation.md`

---

## Phase 1: Compile-Time Safety (8 hours)

### Task 1.1: Audit Catch-All Patterns (30 min)
- [ ] Create `scripts/audit_backend_catchalls.spl`
- [ ] Run audit script
- [ ] Document findings in `doc/audit/catchall_audit_2026-01-31.txt`

### Task 1.2: Remove LLVM Catch-Alls (4 hours)
- [ ] File: `rust/compiler/src/codegen/llvm/functions.rs` line 393-395
- [ ] List all SIMD instructions as unsupported
- [ ] List all concurrency instructions as unsupported
- [ ] List all GPU instructions as unsupported
- [ ] Provide clear error messages with alternative backends
- [ ] Verify: `cargo build --all-features`

### Task 1.3: Remove Vulkan Catch-Alls (2 hours)
- [ ] File: `rust/compiler/src/codegen/vulkan/spirv_instructions.rs` line 154
- [ ] List all CPU-only instructions as unsupported
- [ ] List all I/O instructions as unsupported
- [ ] Categorize unsupported by reason
- [ ] Verify: `cargo build --features vulkan`

### Task 1.4: Add Exhaustiveness Lints (10 min)
- [ ] Add to `rust/compiler/src/codegen/llvm/mod.rs`:
  ```rust
  #![deny(unreachable_patterns)]
  #![warn(clippy::wildcard_enum_match_arm)]
  ```
- [ ] Add to `rust/compiler/src/codegen/vulkan/mod.rs` (same)
- [ ] Verify: `cargo clippy --all-features`

### Task 1.5: Create Validation Tool (1.5 hours)
- [ ] Create `src/compiler/backend/exhaustiveness_validator.spl`
- [ ] Create `test/compiler/backend/exhaustiveness_validator_spec.spl`
- [ ] Test: `./bin/wrappers/simple test test/compiler/backend/exhaustiveness_validator_spec.spl`

### Task 1.6: Verify Success (30 min)
- [ ] Add dummy `MirInst::TestDummy` variant
- [ ] Verify compilation fails with clear error
- [ ] Remove dummy variant
- [ ] Document results in `doc/plan/phase1_completion.md`

---

## Phase 2: Testing Infrastructure (24 hours)

### Task 2.1: MIR Test Builder (4 hours)
- [ ] Create `src/compiler/backend/mir_test_builder.spl`
- [ ] Implement builder pattern for all instruction types
- [ ] Create `all_instruction_tests()` generator
- [ ] Test: Create and compile a simple MIR function

### Task 2.2: Instruction Coverage Tests (8 hours)
- [ ] Create `test/compiler/backend/instruction_coverage_spec.spl`
- [ ] Write specs for Cranelift (all instructions)
- [ ] Write specs for LLVM (supported instructions)
- [ ] Write specs for Vulkan (GPU instructions)
- [ ] Test: `./bin/wrappers/simple test test/compiler/backend/instruction_coverage_spec.spl`

### Task 2.3: Differential Testing (6 hours)
- [ ] Create `test/compiler/backend/differential_testing_spec.spl`
- [ ] Test arithmetic operations (Cranelift vs LLVM)
- [ ] Test control flow (Cranelift vs LLVM)
- [ ] Test memory operations (Cranelift vs LLVM)
- [ ] Add performance benchmarks (optional)

### Task 2.4: Test Generator (4 hours)
- [ ] Create `src/compiler/backend/test_generator.spl`
- [ ] Generate constant tests
- [ ] Generate arithmetic tests
- [ ] Generate GPU tests
- [ ] Generate comprehensive suite

### Task 2.5: CI Integration (2 hours)
- [ ] Create `.github/workflows/backend-completeness.yml`
- [ ] Add to `Makefile`: `test-backends` target
- [ ] Verify CI runs on push
- [ ] Document CI setup in `doc/plan/ci_integration.md`

---

## Phase 3: Documentation (16 hours)

### Task 3.1: Capability Tracker (6 hours)
- [ ] Create `src/compiler/backend/capability_tracker.spl`
- [ ] Implement `BackendCapabilities` class
- [ ] Implement auto-detection from source code
- [ ] Add `to_markdown()` method
- [ ] Test: Generate capabilities for Cranelift

### Task 3.2: Matrix Builder (4 hours)
- [ ] Create `src/compiler/backend/matrix_builder.spl`
- [ ] Implement `BackendMatrixBuilder` class
- [ ] Generate comparison matrix
- [ ] Calculate coverage statistics
- [ ] Test: Build matrix for all backends

### Task 3.3: Doc Generator CLI (4 hours)
- [ ] Create `scripts/generate_backend_docs.spl`
- [ ] Implement matrix generation
- [ ] Implement capability docs generation
- [ ] Implement stats generation
- [ ] Test: `./bin/wrappers/simple scripts/generate_backend_docs.spl all`

### Task 3.4: SSpec Verification (2 hours)
- [ ] Create `test/compiler/backend/documentation_spec.spl`
- [ ] Test matrix accuracy
- [ ] Test coverage calculations
- [ ] Test markdown output validity

---

## Phase 4: DSL Code Generation (40 hours)

### Task 4.1: DSL Design (8 hours)
- [ ] Create `doc/design/ir_dsl_syntax.md`
- [ ] Define instruction definition syntax
- [ ] Define backend lowering syntax
- [ ] Define unsupported instruction syntax
- [ ] Review with stakeholders

### Task 4.2: DSL Parser (12 hours)
- [ ] Create `src/compiler/irdsl/parser.spl`
- [ ] Implement lexer
- [ ] Implement parser for instruction definitions
- [ ] Implement parser for backend blocks
- [ ] Create `test/compiler/irdsl/dsl_parser_spec.spl`

### Task 4.3: Code Generator (12 hours)
- [ ] Create `src/compiler/irdsl/codegen.spl`
- [ ] Generate `MirInst` enum
- [ ] Generate Cranelift match arms
- [ ] Generate LLVM match arms
- [ ] Generate Vulkan match arms
- [ ] Verify generated code compiles

### Task 4.4: Completeness Validator (4 hours)
- [ ] Create `src/compiler/irdsl/validator.spl`
- [ ] Check all backends defined
- [ ] Check no duplicate instructions
- [ ] Check type consistency
- [ ] Create `test/compiler/irdsl/validator_spec.spl`

### Task 4.5: Migration (4 hours)
- [ ] Create `instructions.irdsl` with 10 sample instructions
- [ ] Generate code: `./bin/wrappers/simple src/compiler/irdsl/main.spl`
- [ ] Verify generated code matches handwritten
- [ ] Document migration process
- [ ] Plan incremental migration

---

## Progress Tracking

### Overall Progress
- [ ] Phase 1: Compile-time safety
- [ ] Phase 2: Testing infrastructure
- [ ] Phase 3: Documentation
- [ ] Phase 4: DSL code generation

### Weekly Goals
- **Week 1:** Phase 1 complete
- **Week 2-3:** Phase 2 complete
- **Week 4:** Phase 3 complete
- **Week 5-6:** Phase 4 complete

### Blockers
- None currently

### Notes
- All implementation should prioritize Simple code over Rust
- SSpec tests are mandatory for all new functionality
- Documentation should be auto-generated where possible
- Code generation (Phase 4) can be deferred if needed

---

## Verification Commands

```bash
# Phase 1
make check-exhaustiveness
cargo build --all-features
cargo clippy --all-features

# Phase 2
./bin/wrappers/simple test test/compiler/backend/

# Phase 3
./bin/wrappers/simple scripts/generate_backend_docs.spl all

# Phase 4
./bin/wrappers/simple src/compiler/irdsl/main.spl

# Full pipeline
make backend-completeness-full
```

---

**Last Updated:** 2026-01-31
**Next Review:** After each phase completion
