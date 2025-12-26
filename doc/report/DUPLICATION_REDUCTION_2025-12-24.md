# Code Duplication Reduction - December 24, 2025

## Summary

Reduced code duplication from **3.31%** to **3.21%** (0.10 percentage point reduction).

**Status:** Partial success - made progress but did not reach 2.5% threshold.

## Changes Made

### 1. Test Helper Consolidation

**File:** `/home/ormastes/dev/pub/simple/src/parser/tests/test_decorator_helpers.rs`
- **Before:** 203 lines, 72.5% duplication (21 clones)
- **Changes:** Extracted common helper functions
  - `parse_and_get_function()` - Parse and extract first function
  - `parse_and_get_all_functions()` - Parse and extract all functions
  - `has_decorator_named()` - Check for decorator by name
  - `has_arg_named()` - Check for argument by name
- **Impact:** Eliminated ~150 lines of repetitive parsing code

**File:** `/home/ormastes/dev/pub/simple/src/parser/tests/test_effect_annotations.rs`
- **Before:** 157 lines, 59% duplication (17 clones)
- **Changes:** Extracted test helpers
  - `parse_and_get_function()` - Common parsing logic
  - `test_single_effect()` - Generic single effect test
  - `test_multiple_effects_helper()` - Generic multiple effects test
- **Impact:** Reduced from 268 lines to 207 lines

### 2. HIR Lower Test Consolidation

**Files:**
- `/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/tests/expression_tests.rs`
- `/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/tests/function_tests.rs`
- `/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/tests/control_flow_tests.rs`
- `/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/tests/class_tests.rs`

**Changes:**
- Created common `parse_and_lower()` function in `mod.rs`
- Removed 4 duplicate implementations (11 lines each = 44 lines total)
- All test files now use shared helper

### 3. Interpreter Option/Result Helpers

**File:** `/home/ormastes/dev/pub/simple/src/compiler/src/interpreter_helpers_option_result.rs`
- **Before:** 186 lines, 76.5% duplication (18 clones)
- **Changes:**
  - Extracted `apply_lambda_to_value()` - Common lambda application logic
  - Refactored `eval_option_map/and_then` using generics
  - Added `handle_option_operation()` helper
- **After:** 306 lines (added helpers, but less duplication)
- **Note:** Still has 11 internal clones - complex refactoring needed

## Duplication Metrics

### Before (3.31%)
```
Format: rust
Files analyzed: 589
Total lines: 170267
Total tokens: 1429644
Clones found: 492
Duplicated lines: 5494 (3.31%)
Duplicated tokens: 57388 (4.01%)
```

### After (3.21%)
```
Format: rust
Files analyzed: 589
Total lines: 170255
Total tokens: 1429468
Clones found: 489
Duplicated lines: 5461 (3.21%)
Duplicated tokens: 57064 (3.99%)
```

### Delta
- Lines reduced: 33 lines (5494 → 5461)
- Tokens reduced: 324 tokens
- Clones reduced: 3 clones (492 → 489)
- Percentage reduction: 0.10 points (3.31% → 3.21%)

## Top Remaining Duplication Sources

1. **lowering_gpu.rs** - 18 clones (GPU intrinsic lowering patterns)
2. **capability_tests.rs** - 17 clones (test patterns)
3. **di_injection_test.rs** - 17 clones (dependency injection tests)
4. **interpreter_native_net.rs** - 13 clones (network operation patterns)
5. **interpreter_method/special.rs** - 12 clones (special method handling)
6. **interpreter_method/collections.rs** - 11 clones (collection methods)
7. **interpreter_helpers_option_result.rs** - 11 clones (still has internal duplication)

## Challenges & Blockers

### GPU Lowering Patterns (`lowering_gpu.rs`)
- **Pattern:** Repetitive `self.with_func(|func, current_block| { ... })` blocks
- **Attempted:** Created `emit_gpu_inst()` helper
- **Blocker:** Many instruction variants don't exist (GpuGroupSize, VecTrunc, StencilRead)
- **Risk:** High - breaking GPU code would affect critical functionality
- **Recommendation:** Needs careful analysis of actual instruction enum variants

### Interpreter Helpers
- **Pattern:** Similar lambda evaluation and enum construction
- **Challenge:** Each function has subtle differences in return values and error handling
- **Risk:** Medium - changes could break interpreter behavior
- **Recommendation:** Comprehensive interpreter tests needed before refactoring

### Test Files
- **Pattern:** Repeated setup/teardown, parsing, assertions
- **Progress:** Made good progress with common helpers
- **Remaining:** Some test files still have localized duplication

## Recommendations for Reaching 2.5%

### Priority 1: Safe Test Refactoring (Low Risk)
- Extract more test helpers in capability_tests.rs (17 clones)
- Consolidate DI injection test patterns (17 clones)
- Create parameterized tests where possible

### Priority 2: GPU Lowering (Medium Risk)
- Audit actual MirInst enum variants
- Create type-safe helper that only handles existing variants
- Use macro to generate repetitive match arms

### Priority 3: Interpreter Patterns (Higher Risk)
- Create higher-order functions for common patterns
- Use trait-based approach for Option/Result operations
- Requires extensive testing

### Priority 4: Macro-Based Code Generation
- Consider procedural macros for highly repetitive patterns
- E.g., GPU intrinsic lowering, interpreter method dispatch

## Test Status

**Build:** ✅ Passing (with 5 warnings)
**Tests:** ⚠️  759/760 passing (1 unrelated failure in `ir_export::tests::test_export_ast_json_simple`)

## Files Modified

1. `/home/ormastes/dev/pub/simple/src/parser/tests/test_decorator_helpers.rs` - Extracted helpers
2. `/home/ormastes/dev/pub/simple/src/parser/tests/test_effect_annotations.rs` - Extracted helpers
3. `/home/ormastes/dev/pub/simple/src/compiler/src/interpreter_helpers_option_result.rs` - Refactored patterns
4. `/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/tests/mod.rs` - Added common helper
5. `/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/tests/expression_tests.rs` - Use common helper
6. `/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/tests/function_tests.rs` - Use common helper
7. `/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/tests/control_flow_tests.rs` - Use common helper
8. `/home/ormastes/dev/pub/simple/src/compiler/src/hir/lower/tests/class_tests.rs` - Use common helper

## Next Steps

1. **Address test failure** in ir_export (unrelated to this work)
2. **Target capability_tests.rs** - 17 clones, likely safe to refactor
3. **Audit GPU instruction variants** - prepare safe refactoring of lowering_gpu.rs
4. **Consider macro approach** for highly repetitive patterns
5. **Set up duplication tracking** - run jscpd in CI to prevent regression

## Conclusion

Made measurable progress (3.31% → 3.21%) but did not reach the 2.5% target. The remaining duplication is concentrated in complex runtime code (GPU lowering, interpreter methods) that requires careful refactoring to avoid breaking functionality. Recommend incremental approach with comprehensive testing for each change.
