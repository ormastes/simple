# Parser Errors Analysis

**Generated:** 2026-01-30
**Total Parser Errors:** 75
**Unique Error Patterns:** 34

---

## Executive Summary

The 75 parser errors fall into **5 main categories** representing **92% of all parser failures**:

| Error Pattern | Count | % | Root Cause |
|--------------|-------|---|------------|
| `Expected expression, found At` | 9 | 12% | `@` operator not parsed |
| `Expected Comma, found Colon` | 8 | 11% | Dict/struct syntax confusion |
| `Expected identifier, found Xor` | 7 | 9% | `xor` keyword context issue |
| `Expected expression, found Indent` | 5 | 7% | Indentation parsing bug |
| `Expected identifier, found Assign` | 3 | 4% | Assignment in wrong context |
| **Subtotal (Top 5)** | **32** | **43%** | - |
| Other patterns (29 types) | 43 | 57% | Various syntax issues |

---

## 🔴 Critical Issue #1: `@` Operator Not Parsed (9 errors)

**Error:** `Expected expression, found At`

**Affected Area:** Machine learning / PyTorch tests (100% of these failures)

**Root Cause:** The `@` matrix multiplication operator is defined but not being parsed in expression context.

### Affected Tests (All PyTorch/ML)
1. activation_spec
2. simple_math_spec
3. linalg_spec
4. dataset_spec
5. recurrent_spec
6. transformer_spec
7. fft_spec
8. autograd_spec
9. custom_autograd_spec

### Example Error Context
```simple
# Likely failing code:
val result = matrix_a @ matrix_b  # ❌ Parser expects expression, sees '@'

# Should be:
val result = A @ B  # Matrix multiplication
```

### Fix Required
**Location:** `src/rust/parser/src/expressions/binary.rs` or similar

**Issue:** `@` token exists in lexer but not in expression parser

**Fix:**
```rust
// Add to binary expression operators:
Token::At => {
    // Parse matrix multiplication
    BinaryOp::MatMul
}
```

**Priority:** 🔴 HIGH - Blocks all ML/PyTorch tests

---

## 🔴 Critical Issue #2: Colon vs Comma in Dict Literals (8 errors)

**Error:** `Expected token: expected Comma, found Colon`

**Affected Area:** Game engine tests (88% of these failures)

**Root Cause:** Python/JS-style dict syntax `{key: value}` vs Simple syntax `{key = value}`

### Affected Tests
1. arg_parsing_spec
2. assets_spec (2 instances)
3. component_spec
4. test_audio_spec
5. material_spec
6. actor_model_spec
7. test_actor_spec (2 instances)

### Example Error Context
```simple
# ❌ WRONG - Python/JavaScript style
val config = {
    name: "player",
    health: 100
}

# ✅ CORRECT - Simple style
val config = {
    name = "player",
    health = 100
}
```

### Fix Options

**Option A: Update Tests (Recommended)**
- Simple and fast
- Enforces consistent syntax
- Estimated time: 15 minutes

**Option B: Support Both Syntaxes**
- Parser accepts both `:` and `=`
- Allows migration period
- Estimated time: 1 hour

**Priority:** 🔴 HIGH - Blocks 8 game engine tests

---

## 🟡 Issue #3: `xor` Keyword Not Recognized (7 errors)

**Error:** `Expected identifier, found Xor`

**Affected Area:** Property testing and config tests

**Root Cause:** `xor` is a keyword for bitwise XOR, but parser expects identifier in certain contexts

### Affected Tests
1. config_env_spec (2 instances)
2. context_pack_spec
3. shrinking_spec
4. generators_spec
5. runner_spec (2 instances)

### Example Error Context
```simple
# Likely issue - xor used as field name or variable:
struct Config:
    xor: bool  # ❌ 'xor' is a keyword, can't use as identifier

# Or in pattern matching:
match value:
    case xor:  # ❌ Parser expects identifier, sees keyword
        ...
```

### Fix Options

**Option A: Make `xor` Contextual Keyword**
- Allow as identifier in non-expression contexts
- Similar to `default`, `where`, etc.

**Option B: Update Tests to Avoid `xor`**
- Rename fields/variables
- Use `xor_flag`, `use_xor`, etc.

**Priority:** 🟡 MEDIUM - Workaround exists (rename)

---

## 🟡 Issue #4: Indent/Dedent Parsing (5 errors)

**Error:** `Expected expression, found Indent` or `found Dedent`

**Affected Area:** UI and AOP tests

**Root Cause:** Parser confused by indentation in certain syntactic contexts

### Affected Tests
1. ui_structural_patchset_spec
2. ui_dynamic_structure_spec
3. aop_around_advice_spec
4. parser_keywords_spec
5. ui_ssr_hydration_spec

### Example Error Context
```simple
# Likely issue - indentation after expression:
val result = if condition:
        value  # ❌ Parser doesn't expect indent here
    else:
        other

# Or multi-line expressions:
val data = [
        1, 2, 3  # ❌ Indent confuses parser
    ]
```

### Fix Required
**Location:** Indentation-sensitive parsing logic

**Investigation Needed:** Read one of the failing files to see exact context

**Priority:** 🟡 MEDIUM - Affects 5 tests in specific domains

---

## 🟡 Issue #5: Assignment in Wrong Context (3 errors)

**Error:** `Expected identifier, found Assign`

**Affected Area:** Game engine tests

**Root Cause:** `=` appearing where identifier expected (possibly in patterns or destructuring)

### Affected Tests
1. assets_spec
2. component_spec
3. input_spec

### Example Error Context
```simple
# Likely issue - assignment in pattern:
match obj:
    case { x = 5 }:  # ❌ Pattern uses =, but should use literal match
        ...

# Or destructuring:
val { x = 10 } = config  # ❌ Wrong syntax
```

### Fix Required
Investigation needed - read failing tests to understand context

**Priority:** 🟡 MEDIUM - Limited to 3 tests

---

## Distribution by Test Location

```
27 × Other locations (various)
14 × tmp/ (temporary test files)
11 × game_engine/
 9 × system/features/
 9 × ml/torch/ (PyTorch)
 3 × ui/
 2 × physics/
```

**Key Insight:** Game engine (11) and ML/PyTorch (9) account for **27% of all parser errors**.

---

## Other Parser Error Patterns (43 errors)

### Medium Frequency (2+ occurrences)
- `Expected Fn, found Static` (2) - Static method syntax
- `Expected expression, found Assign` (2) - Assignment placement
- `Expected pattern, found Val` (2) - Val in pattern context
- `Expected Fn, found Var` (2) - Var in method context
- `Expected Fn, found Colon` (2) - Missing fn keyword
- `Expected pattern, found From` (2) - Import syntax issue
- `Expected Colon, found Not` (2) - Negation placement
- `Expected Comma, found RawString` (2) - String literal syntax
- `Expected RBracket, found Comma` (3) - Array/list syntax

### Low Frequency (1 occurrence each)
29 unique error patterns - each affecting 1 test

---

## Recommended Fix Priority

### Phase 1: High-Impact Fixes (17 errors - 23%)
1. ✅ **Fix `@` operator parsing** - 9 errors (ML/PyTorch)
2. ✅ **Fix dict colon syntax** - 8 errors (Game engine)

**Estimated Time:** 2-3 hours
**Impact:** 23% of parser errors resolved

### Phase 2: Medium-Impact Fixes (15 errors - 20%)
3. ✅ **Fix `xor` keyword context** - 7 errors
4. ✅ **Fix indent/dedent issues** - 5 errors
5. ✅ **Fix assignment context** - 3 errors

**Estimated Time:** 3-4 hours
**Impact:** Additional 20% resolved (43% total)

### Phase 3: Long-Tail Fixes (43 errors - 57%)
6. ✅ **Fix remaining 29 unique patterns**

**Estimated Time:** 8-12 hours (investigate each case)
**Impact:** Remaining 57% resolved (100% total)

---

## Quick Win Opportunities

### 1. Update Test Syntax (No Parser Changes)

**Tests to Update:**
- 8 game engine tests: Change `{key: value}` → `{key = value}`
- 7 property tests: Rename `xor` fields to `xor_flag` or similar

**Estimated Time:** 30 minutes
**Impact:** 15 errors fixed (20% of parser errors)

### 2. Create Test Helpers

Create syntax migration helpers:
```bash
# Auto-fix dict syntax
sed -i 's/{([^:}]*): /{\1 = /g' test/lib/std/unit/game_engine/*.spl

# Rename xor identifiers
sed -i 's/\bxor:/xor_flag:/g' test/lib/std/unit/infra/*.spl
```

---

## Investigation Checklist

### For Each Error Pattern:
- [ ] Read 1-2 failing test files
- [ ] Identify exact syntax causing error
- [ ] Check if it's:
  - [ ] Invalid syntax (fix test)
  - [ ] Unimplemented feature (implement)
  - [ ] Parser bug (fix parser)

### Sample Investigation Commands:
```bash
# Read a failing test
cat test/lib/std/unit/ml/torch/nn/activation_spec.spl | grep -A 3 -B 3 '@'

# Find all @ usages
grep -r '@' test/lib/std/unit/ml/torch/

# Test parser directly
./target/release/simple_old test test/lib/std/unit/ml/torch/nn/activation_spec.spl -vv
```

---

## Estimated Completion Timeline

### Optimistic (Focus on High-Impact)
- **Phase 1:** 2-3 hours → 17 errors fixed (23%)
- **Quick wins:** 30 min → 15 errors fixed (20%)
- **Total:** 3.5 hours → 32 errors fixed (43%)
- **Remaining:** 43 errors (57% - long tail)

### Realistic (All Errors)
- **Phase 1:** 2-3 hours → 17 errors
- **Phase 2:** 3-4 hours → 15 errors
- **Phase 3:** 8-12 hours → 43 errors
- **Total:** 13-19 hours → 75 errors (100%)

### Recommended Approach
Focus on **Phase 1 + Quick Wins** first:
- Fixes 43% of errors
- Unblocks ML/PyTorch and game engine tests
- Can be completed in one working session

---

## Next Steps

1. **Immediate:** Read sample files from top 2 error patterns
   ```bash
   cat test/lib/std/unit/ml/torch/nn/activation_spec.spl | head -50
   cat test/lib/std/unit/game_engine/assets_spec.spl | head -50
   ```

2. **Implement fixes:**
   - Add `@` operator to expression parser
   - Update tests to use `=` instead of `:` in dicts

3. **Run tests to verify:**
   ```bash
   ./target/release/simple_old test test/lib/std/unit/ml/torch/
   ./target/release/simple_old test test/lib/std/unit/game_engine/
   ```

4. **Track progress:**
   - Update this document as errors are fixed
   - Re-run full test suite
   - Update test_result.md

---

## Files for Manual Review

**High Priority:**
- `test/lib/std/unit/ml/torch/nn/activation_spec.spl` - @ operator example
- `test/lib/std/unit/game_engine/assets_spec.spl` - dict colon syntax

**Medium Priority:**
- `test/lib/std/unit/infra/config_env_spec.spl` - xor keyword issue
- `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` - indent issue

---

## Conclusion

**75 parser errors** can be reduced significantly with targeted fixes:

- **17 errors (23%)** - Two main issues: `@` operator and dict syntax
- **15 errors (20%)** - Three medium issues: xor, indent, assignment
- **43 errors (57%)** - Long tail requiring individual investigation

**Recommended immediate action:** Fix `@` operator and dict syntax to unblock ML and game engine test suites.
