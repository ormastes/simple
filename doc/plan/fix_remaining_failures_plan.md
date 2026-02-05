# Fix Plan for Remaining Test Failures

**Date:** 2026-02-05
**Status:** Planning
**Total Failures:** 4,178 tests (26.6%)
**Focus:** System (39), Compiler (31), Build (7) = 77 high-priority failures

---

## Current Status

### Overall Test Results
- **Total:** 15,703 tests
- **Passed:** 11,525 (73.4%)
- **Failed:** 4,178 (26.6%)
- **Failed Files:** 308

### Breakdown by Category
| Category | Failed Files | Priority |
|----------|-------------|----------|
| **lib/** | 160 | Medium |
| **system/** | 39 | 🔴 High |
| **compiler/** | 31 | 🔴 High |
| **app/** | 22 | Medium |
| **build/** | 7 | 🔴 High |
| **specs/** | 13 | Low |
| **diagnostics/** | 7 | Medium |
| **integration/** | 6 | Medium |
| **other** | 23 | Low |

---

## Priority 1: System Tests (39 failures)

### Collections Tests
**Files:**
- `test/system/collections/hashmap_basic_spec.spl` (5 passed, 3 failed)
- `test/system/collections/hashset_basic_spec.spl`
- `test/system/collections/btree_basic_spec.spl`

**Status:** Partially working (Pure Simple implementation)

**Issues:**
1. HashMap test expects FFI-based implementation but gets Pure Simple
2. Some methods may have different signatures
3. Tests may use `.new()` constructor pattern

**Fix Plan:**
```
1. Read failing test details for each collection
2. Identify signature mismatches
3. Options:
   a) Update Pure Simple implementation to match expected API
   b) Update tests to use Pure Simple API
   c) Add adapter layer for compatibility
4. Remove @pending markers
5. Verify all tests pass
```

**Estimated Time:** 1-2 hours

---

## Priority 2: Compiler Tests (31 failures)

### Categories:
1. **Backend tests** (9 files)
   - backend_capability, backend_orchestration, differential_testing
   - exhaustiveness_validator, instruction_coverage
   - native_bridge, native_ffi, orchestration_ffi_test

2. **Block tests** (3 files)
   - block_definition_three_level, block_outline_info, block_skip_policy

3. **Core compiler** (19 files)
   - bidir_type_check, borrow_check, driver
   - effect_inference, error_formatter, hir_lowering
   - import_resolution, import_warning
   - lexer (4 files), match_empty_array_bug
   - mir_opt, resolve, type_infer_comprehensive

**Common Issues:**
- Missing implementations (stubs/TODOs)
- API changes not reflected in tests
- Dependency on Rust FFI not available in Pure Simple mode

**Fix Strategy:**

### Phase 1: Identify Failure Patterns
```bash
# Sample 5 tests from each category
for test in backend/backend_capability blocks/block_outline lexer_spec; do
    ./bin/simple_runtime test test/compiler/$test_spec.spl 2>&1 | grep "Error:"
done
```

### Phase 2: Categorize Failures
- **Type A:** Missing implementation (need to implement)
- **Type B:** API mismatch (need to update test or impl)
- **Type C:** FFI dependency (need Pure Simple alternative)
- **Type D:** Test infrastructure issue (need to fix test framework)

### Phase 3: Fix by Type
```
Type A: Implement missing features
Type B: Align API signatures
Type C: Create Pure Simple alternatives or mark @pending
Type D: Fix test framework issues
```

**Estimated Time:** 3-4 hours

---

## Priority 3: Build Tests (7 failures)

### Files:
- `test/build/advanced_spec.spl` - Error: `MetricsConfig` not found
- `test/build/bootstrap_spec.spl`
- `test/build/cargo_spec.spl`
- `test/build/coverage_spec.spl`
- `test/build/package_spec.spl`
- `test/build/quality_spec.spl`
- `test/build/test_integration_spec.spl`

**Root Cause:** Build system tests expect specific classes/functions that may not be exported

**Fix Plan:**

### Step 1: Check Missing Exports
```bash
# Find what MetricsConfig should be
grep -r "MetricsConfig" src/app/build/

# Check exports in build modules
grep "^export" src/app/build/*.spl
```

### Step 2: Add Missing Exports
```simple
# In src/app/build/advanced.spl (or appropriate file)
export MetricsConfig, BuildMetrics, ...
```

### Step 3: Verify Each Test
```bash
for test in test/build/*_spec.spl; do
    ./bin/simple_runtime test $test 2>&1 | grep -E "PASSED|FAILED|Error:"
done
```

**Estimated Time:** 1 hour

---

## Implementation Plan

### Week 1: High Priority (System, Build)

**Day 1: System Collections (4 hours)**
- [ ] Analyze hashmap_basic_spec failures
- [ ] Fix Pure Simple HashMap to match expected API
- [ ] Test and verify HashMap passes
- [ ] Repeat for HashSet
- [ ] Repeat for BTreeMap

**Day 2: Build Tests (2 hours)**
- [ ] Identify all missing exports in build system
- [ ] Add exports to appropriate modules
- [ ] Verify all 7 build tests pass

### Week 2: Compiler Tests

**Day 3-4: Backend Tests (8 hours)**
- [ ] Sample and categorize all 9 backend test failures
- [ ] Implement missing backend features
- [ ] Fix API mismatches
- [ ] Create Pure Simple alternatives where needed

**Day 5-6: Core Compiler Tests (8 hours)**
- [ ] Sample and categorize 19 core compiler failures
- [ ] Fix lexer issues (4 tests)
- [ ] Fix type system issues (bidir, type_infer)
- [ ] Fix import/resolve issues
- [ ] Fix MIR/HIR issues

**Day 7: Block Tests (2 hours)**
- [ ] Fix 3 block-related tests

---

## Detailed Investigation Steps

### For Each Failed Test:

```bash
# 1. Run test and capture full output
./bin/simple_runtime test <test_file> 2>&1 > /tmp/test_output.txt

# 2. Identify error type
grep -E "Error:|not found|undefined" /tmp/test_output.txt

# 3. Find source of issue
# - Missing implementation?
# - API mismatch?
# - Missing export?
# - Test infrastructure?

# 4. Fix appropriately
# - Implement feature
# - Update API
# - Add export
# - Fix test framework

# 5. Verify fix
./bin/simple_runtime test <test_file> 2>&1 | grep "PASSED"

# 6. Document fix
echo "Fixed: <issue> in <file>" >> doc/plan/fixes_applied.md
```

---

## Risk Assessment

### High Risk (may require significant work):
- ❌ **Compiler backend tests** - May need Rust FFI implementations
- ❌ **Type system tests** - Complex implementation required
- ⚠️ **Lexer tests** - Parser changes may break tests

### Medium Risk:
- ⚠️ **Collections tests** - API alignment needed
- ⚠️ **Build tests** - Export issues only

### Low Risk:
- ✅ **System tests** - Mostly implementation complete
- ✅ **Block tests** - Small scope

---

## Success Criteria

### Phase 1 Complete (Week 1):
- [ ] System collection tests: 0 failures (was 3)
- [ ] Build tests: 0 failures (was 7)
- [ ] **Total reduction:** ~40 failures

### Phase 2 Complete (Week 2):
- [ ] Compiler backend tests: <3 failures (was 9)
- [ ] Compiler core tests: <5 failures (was 19)
- [ ] Compiler block tests: 0 failures (was 3)
- [ ] **Total reduction:** ~64 failures

### Overall Goal:
- **Start:** 4,178 failures (26.6%)
- **Target:** <4,000 failures (<25%)
- **Stretch:** <3,500 failures (<22%)

---

## Quick Wins (Do First)

These can be fixed quickly for immediate impact:

1. **Build exports** (~1 hour)
   - Add missing `MetricsConfig` and related exports
   - Should fix all 7 build tests

2. **Collection @pending markers** (~30 min)
   - Remove @pending from working collection tests
   - May immediately pass some tests

3. **Test database corruption** (~15 min)
   - Fix "Invalid table row: expected 2 columns, found 1"
   - Blocking test result tracking

---

## Next Actions

### Immediate (This Session):
```bash
# 1. Fix test database corruption
# Check doc/test/test_db.sdn format
# Fix malformed rows

# 2. Check collection test details
./bin/simple_runtime test test/system/collections/hashmap_basic_spec.spl 2>&1 > /tmp/hashmap_test.txt
# Read failures and identify fixes needed

# 3. Fix build exports
grep -r "MetricsConfig\|BuildMetrics" src/app/build/
# Add missing exports
```

### This Week:
- Focus on System and Build categories
- Target: 40+ fewer failures

### Next Week:
- Focus on Compiler category
- Target: 60+ fewer failures

---

## Tracking Progress

Create tracking file: `doc/plan/fix_progress.md`

```markdown
# Fix Progress Tracker

## Session 1 (2026-02-05)
- [x] Analyzed failure categories
- [x] Created fix plan
- [ ] Fixed test database corruption
- [ ] Fixed build exports (0/7)
- [ ] Fixed collection tests (0/3)

## Session 2
...
```

---

## Conclusion

**Total Target:** Fix 77 high-priority failures (System: 39, Compiler: 31, Build: 7)

**Strategy:**
1. Quick wins first (build exports)
2. System tests (collections API alignment)
3. Compiler tests (categorize and fix by type)

**Expected Outcome:**
- Reduce failures from 4,178 → ~4,000 (4% reduction)
- Demonstrate clear path to <3,500 failures
- Establish fix patterns for remaining categories

**Ready to begin:** ✅
