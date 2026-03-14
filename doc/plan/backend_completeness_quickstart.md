# Backend Completeness - Quick Start Guide

**Full Plan:** `doc/plan/backend_completeness_full_implementation.md`
**Date:** 2026-01-31

---

## TL;DR

Implementing all 4 phases to prevent missing backend codegen:
1. **Exhaustive matching** (Rust) - Compile-time safety
2. **Testing** (SSpec) - Runtime verification
3. **Documentation** (Simple) - Auto-generated tracking
4. **DSL** (Simple) - Code generation from declarative specs

**Total Effort:** ~88 hours over 6 weeks

---

## Quick Commands

```bash
# Phase 1: Check exhaustiveness
make check-exhaustiveness

# Phase 2: Run backend tests
make test-backends

# Phase 3: Generate docs
make docs-backends

# Phase 4: Regenerate from DSL
make codegen-from-dsl

# Full pipeline
make backend-completeness-full
```

---

## File Structure

### Phase 1 (Rust - Manual)
- `rust/compiler/src/codegen/llvm/functions.rs` - Remove catch-alls
- `rust/compiler/src/codegen/vulkan/spirv_instructions.rs` - Remove catch-alls
- `src/compiler/backend/exhaustiveness_validator.spl` - Validation tool

### Phase 2 (Simple - SSpec Tests)
- `test/compiler/backend/instruction_coverage_spec.spl` - Coverage tests
- `test/compiler/backend/differential_testing_spec.spl` - Equivalence tests
- `src/compiler/backend/mir_test_builder.spl` - Test generator
- `src/compiler/backend/test_generator.spl` - Auto-generate test cases

### Phase 3 (Simple - Documentation)
- `src/compiler/backend/capability_tracker.spl` - Track support
- `src/compiler/backend/matrix_builder.spl` - Support matrix
- `scripts/generate_backend_docs.spl` - CLI tool
- `doc/backend/BACKEND_SUPPORT_MATRIX.md` - Generated output

### Phase 4 (Simple - DSL)
- `instructions.irdsl` - Instruction definitions (DSL)
- `src/compiler/irdsl/parser.spl` - DSL parser
- `src/compiler/irdsl/codegen.spl` - Code generator
- `src/compiler/irdsl/validator.spl` - Completeness checker
- Generated: `rust/compiler/src/mir/inst_enum.rs` (and backends)

---

## Implementation Order

### Week 1: Phase 1 (8 hours)
**Goal:** Compile-time safety

1. Audit catch-alls: `simple scripts/audit_backend_catchalls.spl`
2. Remove LLVM catch-alls (4 hours)
3. Remove Vulkan catch-alls (2 hours)
4. Add lints + verification (2 hours)

**Success:** Adding new `MirInst` fails compilation

### Weeks 2-3: Phase 2 (24 hours)
**Goal:** Runtime verification

1. Build MIR test infrastructure (6 hours)
2. Write instruction coverage specs (8 hours)
3. Write differential testing specs (6 hours)
4. CI integration (4 hours)

**Success:** All 80+ instructions tested, CI passes

### Week 4: Phase 3 (16 hours)
**Goal:** Documentation tracking

1. Capability tracker (6 hours)
2. Matrix builder (4 hours)
3. Doc generator CLI (4 hours)
4. SSpec verification (2 hours)

**Success:** Auto-generated docs stay in sync

### Weeks 5-6: Phase 4 (40 hours)
**Goal:** DSL-based generation

1. Design DSL syntax (8 hours)
2. Implement parser (12 hours)
3. Implement code generator (12 hours)
4. Validation + migration (8 hours)

**Success:** Generated code is exhaustive, time to add instruction < 15min

---

## Key Design Decisions

### Simple-First Strategy
- **Testing:** All test infrastructure in Simple/SSpec
- **Documentation:** Tracking and generation in Simple
- **DSL:** Parser and codegen in Simple
- **Rust:** Only for low-level backend code

**Rationale:** Simple is the target language, tooling should be self-hosted.

### Intensive SSpec Verification
- Coverage tests for all 80+ instructions
- Differential tests (Cranelift vs LLVM)
- Performance benchmarks
- Documentation accuracy tests

**Rationale:** Tests are executable specifications.

### Phased Approach
- Each phase builds on previous
- Can stop after any phase
- Phases 1-3 are essential, Phase 4 is optimization

**Rationale:** Deliver value incrementally.

---

## Success Criteria

### Overall
- [ ] **Compile-time:** New instruction = compilation failure
- [ ] **Runtime:** All instructions tested in all backends
- [ ] **Documentation:** Auto-generated, always in sync
- [ ] **Efficiency:** Adding instruction takes < 15 minutes

### Phase-Specific
- [ ] **Phase 1:** Zero catch-all patterns
- [ ] **Phase 2:** 100% test coverage
- [ ] **Phase 3:** Docs update automatically
- [ ] **Phase 4:** DSL generates valid Rust

---

## Next Actions

1. ✅ Read this document (you are here!)
2. [ ] Review full plan: `doc/plan/backend_completeness_full_implementation.md`
3. [ ] Create branch: `git checkout -b feature/backend-completeness`
4. [ ] Start Phase 1: Remove catch-alls
5. [ ] Run verification: `make check-exhaustiveness`

---

## Questions?

- **Full details:** See `doc/plan/backend_completeness_full_implementation.md`
- **Research:** See `doc/research/multi_backend_instruction_completeness.md`
- **Summary:** See `doc/research/backend_completeness_summary.md`
