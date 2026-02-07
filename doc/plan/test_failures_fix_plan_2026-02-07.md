# Test Failures - Comprehensive Fix Plan

**Date:** 2026-02-07
**Status:** Planning
**Current State:** 355 failing tests out of 903 (60.7% pass rate)
**Target:** 95%+ pass rate

---

## Executive Summary

### Failure Distribution

| Category | Count | % of Failures | Priority |
|----------|-------|---------------|----------|
| **lib** | 169 | 47.6% | Medium |
| **other** | 75 | 21.1% | Low |
| **system** | 53 | 14.9% | High |
| **std** | 15 | 4.2% | High |
| **app** | 14 | 3.9% | High |
| **specs** | 13 | 3.7% | Medium |
| **integration** | 4 | 1.1% | High |
| **interpreter subsystems** | 12 | 3.4% | Medium |

### Error Types

| Type | Count | % | Fix Approach |
|------|-------|---|--------------|
| **runtime_error** | 315 | 88.7% | Investigate + Fix |
| **semantic_error** | 24 | 6.8% | Fix compiler/runtime |
| **parse_error** | 11 | 3.1% | Fix parser |
| **compile_error** | 5 | 1.4% | Fix compilation |

---

## Phase 1: Critical Parser Fixes (11 files - 3.1%)

**Impact:** Unblocks tests, fixes syntax support
**Effort:** 2-3 days
**Priority:** 🔴 CRITICAL

### Issues

1. **`Assert` keyword not recognized** (2 files)
   ```
   test/app/build/link_bins_spec.spl
   test/app/utils/colors_spec.spl
   ```
   **Fix:** Add `Assert` as reserved keyword or fix parser to handle it in expression context

2. **`Indent` token unexpected** (2 files)
   ```
   test/lib/std/integration/failsafe/crash_prevention_spec.spl
   test/lib/std/integration/failsafe/failsafe_integration_spec.spl
   ```
   **Fix:** Fix indentation handling in try/catch or error blocks

3. **`Mixin` keyword in pattern** (1 file)
   ```
   test/lib/std/type_checker/type_inference_spec.spl
   ```
   **Fix:** Either implement Mixin support or fix pattern matching

4. **`Spawn` keyword as identifier** (1 file)
   ```
   test/lib/std/unit/async_spec.spl
   ```
   **Fix:** Make `spawn` contextual keyword, not reserved

5. **Other parse errors** (5 files)
   - Pattern syntax issues
   - Expression parsing bugs
   - **Action:** Review each file individually

### Implementation Steps

1. **Add Assert support**
   ```simple
   # In parser, add Assert to contextual keywords
   # Or allow Assert in expression position
   ```

2. **Fix Indent handling**
   ```simple
   # Review indentation state machine
   # Fix block detection after certain keywords
   ```

3. **Make keywords contextual**
   ```simple
   # spawn, assert, etc. should be contextual
   # Not reserved keywords everywhere
   ```

---

## Phase 2: Semantic Analysis Fixes (24 files - 6.8%)

**Impact:** Fixes type checking, name resolution
**Effort:** 3-4 days
**Priority:** 🔴 CRITICAL

### Issue 1: Type Mismatch - Dict to Int (4 files)

```
test/app/formatter_minimal_spec.spl
test/app/lint_simple_spec.spl
test/app/lint_spec.spl (runtime)
test/app/test_analysis_spec.spl
```

**Pattern:**
```
Error: semantic: type mismatch: cannot convert dict to int
```

**Root Cause:** Likely using dict literal where struct construction expected

**Fix:**
1. Check if these tests use old `.new()` pattern
2. Update to direct construction: `Type(field: value)`
3. Or fix type inference for dict → struct conversion

### Issue 2: Unsupported Path Call (1 file)

```
test/lib/std/features/resource_cleanup_spec.spl
Error: semantic: unsupported path call: ["ResourceRegistry", "clear"]
```

**Fix:** Static method desugaring (already completed per memory notes)
- Verify desugaring is applied to this file
- If still failing, debug desugaring pass

### Issue 3: Variable/Function Not Found (5 files)

```
test/app/interpreter/helpers/debug_spec.spl - variable `from` not found
test/integration/cli_dispatch_spec.spl - variable `COMMAND_TABLE` not found
test/lib/std/features/bootstrap_spec.spl - function `background` not found
test/lib/std/system/feature_doc_spec.spl - function `clear_feature_registry` not found
test/lib/std/unit/compiler/generic_template_spec.spl - variable `partition_generic_constructs` not found
```

**Fixes:**
1. **`from` variable** - Deprecated `from ... import` syntax issue
   - **Action:** Migrate to `use` syntax
2. **Missing constants/functions** - Not exported or moved
   - **Action:** Check exports, add missing functions, or update tests

### Implementation Steps

1. **Dict-to-int conversion**
   ```bash
   # Check each file for constructor patterns
   grep "\.new()" test/app/formatter_minimal_spec.spl
   grep "\.new()" test/app/lint_simple_spec.spl
   grep "\.new()" test/app/test_analysis_spec.spl
   # Replace with direct construction
   ```

2. **Static method calls**
   ```bash
   # Verify desugaring runs on these files
   bin/simple desugar test/lib/std/features/resource_cleanup_spec.spl
   ```

3. **Import migration**
   ```bash
   # Find all `from ... import` usage
   grep -r "from .* import" test/
   # Replace with `use` syntax
   ```

---

## Phase 3: Compile Errors (5 files - 1.4%)

**Impact:** Fixes source file issues blocking compilation
**Effort:** 1 day
**Priority:** 🔴 CRITICAL

### Issue: Parse Error in Source File

```
test/lib/std/features/table_spec.spl
Error: compile failed: parse: in "/home/ormastes/dev/pub/simple/src/std/src/table.spl":
  Unexpected token: expected expression, found Val
```

**Root Cause:** Bug in `src/std/src/table.spl` source file

**Fix:**
1. Open `/home/ormastes/dev/pub/simple/src/std/src/table.spl`
2. Find line with `Val` token issue
3. Fix syntax (likely misplaced `val` keyword)

**Other compile errors:** Check remaining 4 files for similar source file bugs

---

## Phase 4: Runtime Errors - High Priority (50 files)

**Impact:** Core functionality tests
**Effort:** 2 weeks
**Priority:** 🟡 HIGH

### Subcategories

#### 4.1 App Tests (14 files)
- **mcp/**, **package/**, **test_runner/** - Missing runtime functions
- **Action:** Implement missing SFFI stubs

#### 4.2 Integration Tests (4 files)
```
database_core_spec.spl
database_e2e_spec.spl
mcp_bugdb_spec.spl
cli_dispatch_spec.spl (already in semantic)
```
- **Action:** Fix database test dependencies, verify MCP integration

#### 4.3 System Tests (53 files)
- Feature tests for advanced language features
- **Action:** Investigate each, categorize by feature

#### 4.4 Std Library Tests (15 files)
- Core standard library functionality
- **Action:** High priority - these are foundational

### Implementation Strategy

1. **Triage:** Run each test individually, capture full error
   ```bash
   bin/simple_runtime test/app/lint_spec.spl 2>&1 | tee /tmp/lint_error.log
   ```

2. **Categorize:**
   - Missing runtime function → Add SFFI stub
   - Test framework issue → Fix test harness
   - Feature not implemented → Add to backlog
   - Bug in test → Fix test

3. **Fix patterns:**
   - **Missing function:** Add to `src/app/io/mod.spl`
   - **Static method:** Verify desugaring
   - **Import error:** Migrate syntax
   - **Test dep missing:** Add or mock

---

## Phase 5: Runtime Errors - Medium Priority (100 files)

**Impact:** Library and feature tests
**Effort:** 3-4 weeks
**Priority:** 🟢 MEDIUM

### Subcategories

#### 5.1 Lib/std/unit Tests (100+ files)
- Compiler infrastructure tests
- Standard library unit tests
- Many are "Unknown error" - need investigation

#### 5.2 Interpreter Subsystem Tests (12 files)
```
async_runtime (3 files)
collections (2 files)
lazy (2 files)
memory (2 files)
core, helpers, perf (3 files)
```

**Strategy:**
1. Pick one subsystem (e.g., collections)
2. Fix all tests in that subsystem
3. Move to next subsystem

---

## Phase 6: Runtime Errors - Low Priority (165 files)

**Impact:** Advanced features, "other" category
**Effort:** 4-6 weeks
**Priority:** ⚪ LOW

### Categories

- **other/** (75 files) - Remote debugging, QEMU, DAP
- **lib/** remaining (69 files) - Advanced compiler features
- **specs/** (13 files) - Legacy/deprecated tests

**Strategy:**
- Fix incrementally as time permits
- Some may be deferred to future releases
- Focus on removing "Unknown error" - add proper error messages

---

## Implementation Priority Matrix

| Phase | Files | Effort | Impact | Priority | Timeline |
|-------|-------|--------|--------|----------|----------|
| **Phase 1** | 11 | 2-3 days | Unblocks many tests | 🔴 CRITICAL | Week 1 |
| **Phase 2** | 24 | 3-4 days | Fixes core issues | 🔴 CRITICAL | Week 1-2 |
| **Phase 3** | 5 | 1 day | Fixes source bugs | 🔴 CRITICAL | Week 1 |
| **Phase 4** | 50 | 2 weeks | Core functionality | 🟡 HIGH | Week 2-4 |
| **Phase 5** | 100 | 3-4 weeks | Library features | 🟢 MEDIUM | Week 4-8 |
| **Phase 6** | 165 | 4-6 weeks | Advanced features | ⚪ LOW | Week 8+ |

**Total:** 355 files, ~12-16 weeks for all phases

---

## Quick Wins (Can Fix Today)

### 1. Static Method Migration (Complete)
- ✅ Desugaring already implemented
- ⏳ Verify it runs on all test files
- ⏳ Re-run tests to see improvement

### 2. Import Syntax Migration (2 hours)
```bash
# Find all deprecated imports
grep -r "from .* import" test/ --include="*.spl"

# Replace pattern:
# from module import func → use module (func)
```

### 3. Dict-to-Int Type Errors (1 hour)
```bash
# Fix the 4 files with dict-to-int conversion
# Replace .new() with direct construction
```

### 4. Parse Error Files (2 hours)
```bash
# Fix Assert keyword issue
# Fix Indent handling
# Add tests to prevent regression
```

**Estimated improvement from quick wins:** +39 tests (11%)

---

## Tracking Progress

### Metrics to Monitor

1. **Pass Rate**
   - Current: 60.7% (548/903)
   - Target: 95%+ (857/903)
   - Improvement needed: +309 tests

2. **Error Type Distribution**
   - Reduce "Unknown error" to <5%
   - Fix all parse/semantic errors (35 files)
   - Systematic runtime error reduction

3. **Category Health**
   - App: 14 → 0 failures
   - Integration: 4 → 0 failures
   - System: 53 → <10 failures
   - Std: 15 → 0 failures

### Progress Reports

Generate weekly:
```bash
bin/simple test 2>&1 | tee test_output.log
python3 analyze_failures.py test_output.log
# Updates doc/test/test_failures_summary.md
```

---

## Risk Analysis

### High Risk

1. **"Unknown error" failures (280 files)**
   - May hide multiple distinct issues
   - Requires manual investigation
   - **Mitigation:** Improve test error reporting first

2. **Feature not implemented**
   - Some tests may be for unimplemented features
   - **Mitigation:** Mark as pending/skip, add to backlog

3. **Test framework bugs**
   - Issues in test harness itself
   - **Mitigation:** Fix test runner before fixing tests

### Medium Risk

1. **Cascading failures**
   - Fixing one issue may reveal others
   - **Mitigation:** Fix in priority order, re-test after each phase

2. **Deprecated tests**
   - Some tests may be obsolete
   - **Mitigation:** Archive if feature is removed

---

## Success Criteria

### Phase 1-3 Complete (Critical Fixes)
- ✅ All parse errors fixed (11 files)
- ✅ All semantic errors fixed (24 files)
- ✅ All compile errors fixed (5 files)
- ✅ Pass rate: 65%+ (587/903)

### Phase 4 Complete (High Priority)
- ✅ App tests passing (14 files)
- ✅ Integration tests passing (4 files)
- ✅ System tests: <20 failures (33+ fixed)
- ✅ Std tests: <5 failures (10+ fixed)
- ✅ Pass rate: 75%+ (677/903)

### Phase 5 Complete (Medium Priority)
- ✅ Lib tests: <50 failures (50+ fixed)
- ✅ Interpreter tests: <5 failures (7+ fixed)
- ✅ Pass rate: 85%+ (767/903)

### All Phases Complete
- ✅ Pass rate: 95%+ (857/903)
- ✅ All "Unknown error" categorized
- ✅ Documentation updated
- ✅ CI/CD passing

---

## Resources Needed

### Tools
1. **Test analyzer** - Categorize failures automatically ✅ (exists)
2. **Error reporter** - Better test error messages ⏳
3. **Static analysis** - Find deprecated patterns ⏳

### Documentation
1. **Migration guide** - Old syntax → new syntax ⏳
2. **Test writing guide** - Prevent future issues ✅ (exists in skills)
3. **Error reference** - Common errors and fixes ⏳

---

## Next Steps (This Week)

### Monday-Tuesday: Quick Wins
- [ ] Fix import syntax migration (2 hours)
- [ ] Fix dict-to-int type errors (1 hour)
- [ ] Fix Assert/Indent parse errors (2 hours)
- [ ] Re-run tests, measure improvement

### Wednesday-Thursday: Phase 1 Complete
- [ ] Fix remaining parse errors
- [ ] Add parser tests to prevent regression
- [ ] Document parser fixes

### Friday: Phase 2 Start
- [ ] Begin semantic error fixes
- [ ] Fix static method calls
- [ ] Update variable/function not found issues

### Weekend: Planning
- [ ] Review Phase 4 failures
- [ ] Categorize runtime errors
- [ ] Create detailed Phase 4 plan

---

## Appendix A: Failure Database Queries

### Get All Parse Errors
```bash
grep "parse_error" doc/test/test_failures_grouped.sdn | wc -l
```

### Get App Category Failures
```bash
grep "^    [0-9]*, app," doc/test/test_failures_grouped.sdn
```

### Count by Error Type
```bash
for type in parse_error semantic_error compile_error runtime_error; do
  count=$(grep "$type" doc/test/test_failures_grouped.sdn | wc -l)
  echo "$type: $count"
done
```

### List Unknown Errors
```bash
grep "Unknown error" doc/test/test_failures_grouped.sdn | wc -l
```

---

## Appendix B: Common Fix Patterns

### Pattern 1: Static Method Migration
```simple
# Before (fails)
result = MyClass.static_method()

# After (works)
result = MyClass__static_method()  # Desugared
```

### Pattern 2: Import Syntax
```simple
# Before (fails)
from std.collections import List, Dict

# After (works)
use std.collections (List, Dict)
```

### Pattern 3: Constructor
```simple
# Before (may fail)
obj = MyClass.new(field: value)

# After (works)
obj = MyClass(field: value)
```

### Pattern 4: Contextual Keywords
```simple
# Before (fails - spawn is reserved)
val spawn = 5

# After (works - spawn is contextual)
val spawn = 5  # Parser allows this now
```

---

**Status:** Ready for implementation
**Owner:** Development team
**Review Date:** 2026-02-14 (one week from start)
