# Test Revival Plan - 2026-01-29

## Executive Summary

**Total Disabled Tests Found:**
- **8** Rust tests with `#[ignore]`
- **582** Simple tests with `tag: [skip]`
- **20** Rust tests commented out (`// #[test]`)
- **~1500** Simple test functions commented out

**Total to Revive:** ~2,110 tests

## Categories & Priority

### Priority 1: Quick Wins (Easy to Revive)

#### A. Rust Commented Tests (20 tests)
**Location:** Type inference, runtime collections, driver operators

**Tests:**
1. `src/rust/type/tests/inference.rs` (5 tests)
   - `infers_range_expression` - Requires range operator support
   - `infers_bitwise_operators` - Requires bitwise ops
   - `infers_or_pattern` - Requires or patterns
   - `infers_match_expression_as_value` - Requires match expressions

2. `src/rust/runtime/src/value/collection_tests.rs` (3 tests)
   - `test_array_growth` - Array reallocation
   - `test_tuple_default_nil` - Tuple defaults
   - `test_dict_growth` - Dict reallocation

3. `src/rust/driver/tests/runner_operators_tests.rs` (11 tests)
   - `runner_handles_futures`
   - `runner_handles_generators`
   - `runner_handles_impl_blocks`
   - `runner_handles_context_blocks`
   - `runner_handles_macro_expansion`
   - `runner_handles_array_push`
   - `runner_handles_array_functional_methods`
   - `runner_handles_pointer_types`
   - `runner_handles_union_types`
   - `runner_handles_functional_update`
   - `runner_handles_method_missing`

4. `src/rust/driver/tests/include/_effects_tests_basic.rs` (1 test)
   - `effects_async_blocks_blocking_recv`

**Action:** Uncomment and test if feature is implemented. If not, leave commented with clear TODO.

#### B. Simple Tests with Skip Tags (582 tests)

**Files with skip tags:**
1. `test/lib/std/unit/hir/hir_eval_spec.spl`
2. `test/lib/std/unit/hir/hir_lower_spec.spl`
3. `test/lib/std/unit/hir/hir_module_spec.spl`
4. `test/lib/std/unit/hir/hir_types_spec.spl`
5. `test/lib/std/unit/parser/treesitter_lexer_real_spec.spl`
6. `test/lib/std/unit/parser/treesitter_parser_real_spec.spl`
7. `test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl`
8. `test/lib/std/unit/parser/treesitter_tree_real_spec.spl`
9. `test/system/features/classes/classes_spec.spl`
10. `test/system/features/contracts/class_invariant_spec.spl`
11. `test/system/features/treesitter/treesitter_cursor_spec.spl`
12. `test/system/features/treesitter/treesitter_error_recovery_spec.spl`
13. `test/system/features/treesitter/treesitter_query_spec.spl`
14. `test/system/features/treesitter/treesitter_tree_spec.spl`

**Action:** Remove `tag: [skip]` and run tests. Fix failures or re-skip with clear reason.

### Priority 2: Infrastructure-Dependent (Hard)

#### A. Rust #[ignore] Tests (8 tests)

**Location:** `src/rust/compiler/tests/`

1. `generic_template_tests.rs:457` - `test_compile_with_templates_to_smf`
   - **Reason:** Requires full SMF writing integration
   - **Blocker:** SMF writer not complete

2. `generic_template_tests.rs:469` - `test_load_templates_from_smf`
   - **Reason:** Requires SMF loader
   - **Blocker:** SMF loader not implemented

3. `generic_template_tests.rs:479` - `test_link_with_templates`
   - **Reason:** Requires full linker integration
   - **Blocker:** Linker not complete

4. `smf_template_integration_tests.rs:191` - Unknown test
   - **Reason:** Requires SMF symbol table parsing
   - **Blocker:** SMF infrastructure

**Action:** Document blockers, keep ignored until infrastructure ready.

### Priority 3: Commented Simple Tests (~1500 tests)

**Status:** Needs deeper analysis to understand why commented.

**Typical reasons:**
- Incomplete feature implementation
- Syntax not yet supported
- Runtime function not implemented
- Test framework limitation

**Action:** Sample analysis of 10-20 files to understand patterns, then bulk approach.

## Implementation Strategy

### Phase 1: Rust Commented Tests (Week 1)

**Goal:** Revive or document all 20 Rust commented tests

1. **Day 1-2:** Type inference tests (5 tests)
   - Check if ranges, bitwise, or-patterns implemented
   - Uncomment if yes, test, fix if needed
   - If not implemented, add clear TODO comment

2. **Day 3:** Runtime collection tests (3 tests)
   - Check array/dict growth implementation
   - Test growth behavior
   - Enable if working

3. **Day 4-5:** Runner operator tests (11 tests)
   - Check which operators/features are implemented
   - Enable working tests
   - Document blockers for non-working

**Expected Outcome:** 10-15 tests revived, 5-10 documented as blocked

### Phase 2: Simple Skip-Tagged Tests (Week 2-3)

**Goal:** Remove skip tags where tests should pass

1. **HIR Tests** (4 files, ~200 tests)
   - Run without skip, see what passes
   - Fix simple failures
   - Re-skip complex failures with reasons

2. **TreeSitter Tests** (8 files, ~300 tests)
   - Check if TreeSitter bindings work
   - Enable working tests
   - Document FFI/binding requirements

3. **Feature Tests** (2 files, ~82 tests)
   - Classes, contracts tests
   - Enable if features work
   - Fix or document

**Expected Outcome:** 200-300 tests revived, 200-282 remain skipped with clear reasons

### Phase 3: Sample Commented Simple Tests (Week 4)

**Goal:** Understand patterns and create bulk approach

1. Sample 20 files
2. Identify common reasons for commenting
3. Create categories
4. Design bulk revival strategy

**Expected Outcome:** Strategy for Phase 4

### Phase 4: Bulk Simple Test Revival (Ongoing)

Based on Phase 3 findings.

## Success Metrics

### Short Term (2 weeks)
- ✅ 20 Rust commented tests: revived or documented
- ✅ 100+ Simple skip-tagged tests revived
- ✅ Clear documentation for all #[ignore] tests

### Medium Term (1 month)
- ✅ 300+ Simple tests revived
- ✅ Test revival process documented
- ✅ Automated tooling for bulk operations

### Long Term (3 months)
- ✅ 80% of commented tests either revived or documented with clear blockers
- ✅ No tests commented without reason
- ✅ CI checks for undocumented skips

## Tools Needed

1. **Bulk Skip Remover**
   ```bash
   # Remove skip tags and test
   simple test --remove-skips <file>
   ```

2. **Uncomment Test Tool**
   ```bash
   # Uncomment tests and verify syntax
   simple test --uncomment <file>
   ```

3. **Test Status Reporter**
   ```bash
   # Report on all disabled tests
   simple test --report-disabled
   ```

## Risk Assessment

### Low Risk (Easy wins)
- Commented Rust tests: Just uncomment and test
- Skip-tagged tests: Remove tag and test
- **Mitigation:** Can always re-comment/re-skip

### Medium Risk
- Tests may fail revealing real bugs
- **Mitigation:** Fix bugs (good!), or document and re-skip

### High Risk
- Bulk operations may break many tests
- **Mitigation:** Work file-by-file, commit frequently, use branches

## Decision Points

### When to Re-Skip?
- Feature not implemented
- Test reveals infrastructure limitation
- Test requires external dependencies not available

### When to Delete?
- Test is obsolete
- Feature was removed
- Test duplicates another test

### When to Fix?
- Test reveals real bug
- Quick fix available
- High-value test

## Next Steps

1. ✅ Create this plan
2. ⏭️ Review plan with team
3. ⏭️ Start Phase 1: Rust commented tests
4. ⏭️ Document findings
5. ⏭️ Proceed to Phase 2

## Appendix: Detailed Test Lists

### Rust Commented Tests

**Type Inference (src/rust/type/tests/inference.rs):**
- Line 190: `infers_range_expression`
- Line 275: `infers_bitwise_operators`
- Line 305: `infers_or_pattern`
- Line 475: `infers_match_expression_as_value`
- Line 500: (another test)

**Runtime Collections (src/rust/runtime/src/value/collection_tests.rs):**
- Line 167: `test_array_growth`
- Line 217: `test_tuple_default_nil`
- Line 472: `test_dict_growth`

**Runner Operators (src/rust/driver/tests/runner_operators_tests.rs):**
- Line 147: `runner_handles_futures`
- Line 159: `runner_handles_generators`
- Line 173: `runner_handles_impl_blocks`
- Line 188: `runner_handles_context_blocks`
- Line 199: `runner_handles_macro_expansion`
- Line 289: `runner_handles_array_push`
- Line 299: `runner_handles_array_functional_methods`
- Line 407: `runner_handles_pointer_types`
- Line 416: `runner_handles_union_types`
- Line 431: `runner_handles_functional_update`
- Line 456: `runner_handles_method_missing`

**Effects (src/rust/driver/tests/include/_effects_tests_basic.rs):**
- Line 118: `effects_async_blocks_blocking_recv`

### Rust #[ignore] Tests

**SMF/Templates (src/rust/compiler/tests/):**
- `generic_template_tests.rs:457` - SMF writing
- `generic_template_tests.rs:469` - SMF loader
- `generic_template_tests.rs:479` - Linker
- `smf_template_integration_tests.rs:191` - Symbol table

### Simple Skip-Tagged Files

**HIR Tests:**
- `test/lib/std/unit/hir/hir_eval_spec.spl`
- `test/lib/std/unit/hir/hir_lower_spec.spl`
- `test/lib/std/unit/hir/hir_module_spec.spl`
- `test/lib/std/unit/hir/hir_types_spec.spl`

**TreeSitter Tests:**
- `test/lib/std/unit/parser/treesitter_lexer_real_spec.spl`
- `test/lib/std/unit/parser/treesitter_parser_real_spec.spl`
- `test/lib/std/unit/parser/treesitter_tokenkind_real_spec.spl`
- `test/lib/std/unit/parser/treesitter_tree_real_spec.spl`
- `test/system/features/treesitter/treesitter_cursor_spec.spl`
- `test/system/features/treesitter/treesitter_error_recovery_spec.spl`
- `test/system/features/treesitter/treesitter_query_spec.spl`
- `test/system/features/treesitter/treesitter_tree_spec.spl`

**Feature Tests:**
- `test/system/features/classes/classes_spec.spl`
- `test/system/features/contracts/class_invariant_spec.spl`
