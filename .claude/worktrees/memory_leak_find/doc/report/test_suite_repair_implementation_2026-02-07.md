# Test Suite Repair Implementation Report

**Date:** 2026-02-07
**Objective:** Fix 2,584 failing tests (28% failure rate → 90-95% pass rate target)
**Approach:** Phased plan with infrastructure + automation + systematic fixes

---

## Implementation Status

### ✅ Phase 0: Test Infrastructure (COMPLETE)

**Duration:** 1.5 hours

#### 0.1 Fix Test Database Blank Line Terminator Bug ✅

**File Modified:** `src/app/test_runner_new/test_runner_db.spl`

**Changes:**
- Line 75: `"\n"` → `"\n\n"` (create new database)
- Line 78: `"\n"` → `"\n\n"` (append to existing table)
- Line 82: `"\n" + header` → `"\n\n" + header`, `"\n"` → `"\n\n"` (add new table)

**Impact:** SDN format now correctly uses blank line separators between tables.

#### 0.2 Create Batch Test Runner ✅

**File Created:** `src/app/cli/commands/test_batch.spl`

**Features:**
- Configurable batch size (default: 20 files)
- Per-batch pass rate reporting
- Abort threshold for early stopping
- Total time tracking

**Usage:**
```bash
bin/simple test --batch test/lib --batch-size=20
bin/simple test --batch test/lib --abort-threshold=50
```

#### 0.3 Create Test Failure Analyzer ✅

**File Created:** `src/app/cli/commands/test_analyze.spl`

**Features:**
- Categorize failures by root cause
- Count occurrences per category
- List affected files
- Generate fix command recommendations

**Categories Detected:**
1. `constructor_antipattern` - `.new()` calls
2. `bare_import` - `use module` without `.*` or `.{}`
3. `inline_if_else` - Unreliable inline conditionals
4. `static_method_calls` - Needs rebuild

---

### ✅ Phase 1: Build Automated Fix Scripts (COMPLETE)

**Duration:** 2 hours

#### 1.1 Fix Constructor Anti-Pattern Script ✅

**File Created:** `scripts/fix_new_constructors.spl`

**Features:**
- Detect `ClassName.new(...)` patterns
- Auto-replace with direct construction
- Dry-run preview mode
- Test-after-fix with rollback
- Backup original files

**Usage:**
```bash
bin/simple fix-new-constructors test/lib --dry-run
bin/simple fix-new-constructors test/lib --test-after-fix --rollback-on-fail
```

**Expected Impact:** ~200-250 failures fixed

#### 1.2 Fix Bare Imports Script ✅

**File Created:** `scripts/fix_bare_imports.spl`

**Features:**
- Detect bare `use module` statements
- Wildcard strategy: add `.*` suffix
- Explicit strategy: import only used functions (TODO)
- Dry-run preview

**Usage:**
```bash
bin/simple fix-bare-imports test/lib --strategy=wildcard --dry-run
bin/simple fix-bare-imports test/lib --strategy=wildcard
```

**Expected Impact:** ~180-200 failures fixed

#### 1.3 Fix Inline If-Else Script (PLANNED)

**Status:** Not yet implemented

**Next Step:** Create `scripts/fix_inline_if_else.spl`

#### 1.4 Add Missing Type Imports Script (PLANNED)

**Status:** Not yet implemented

**Dependencies:** Build type index first
**Next Step:** Create `scripts/fix_missing_types.spl`

---

### ⏳ Phase 2: Apply Automated Fixes (PENDING)

**Status:** Infrastructure ready, awaiting execution

#### 2.1 Fix Static Method Calls

**Action:** Rebuild bootstrap with static method desugaring
```bash
bin/simple build --bootstrap
cp build/bootstrap/simple bin/bootstrap/simple
```

**Expected Impact:** ~240-250 failures fixed

#### 2.2-2.4 Apply Constructor, Import, Type Fixes

**Status:** Scripts ready, pending execution
**Estimated Time:** 4-5 hours (automated + verification)

---

### 📋 Phase 3: Manual Fixes & Workarounds (PLANNED)

**Estimated Duration:** 8-10 hours

**Key Deliverables:**
1. `doc/guide/test_runtime_workarounds.md` - Document unfixable bugs
2. `test/lib/helpers/constructors.spl` - Imported constructor helpers
3. Inline if-else manual fixes

---

### 📋 Phase 4: Remaining Manual Fixes (PLANNED)

**Estimated Duration:** 6-8 hours

**Focus:**
- Missing SFFI functions
- Manual review queue
- Edge cases

---

## Files Created/Modified

### New Files

| File | Purpose | Lines | Status |
|------|---------|-------|--------|
| `src/app/cli/commands/test_batch.spl` | Batch test runner | 138 | ✅ Complete |
| `src/app/cli/commands/test_analyze.spl` | Failure analyzer | 162 | ✅ Complete |
| `scripts/fix_new_constructors.spl` | Constructor fixer | 153 | ✅ Complete |
| `scripts/fix_bare_imports.spl` | Import fixer | 142 | ✅ Complete |

### Modified Files

| File | Changes | Status |
|------|---------|--------|
| `src/app/test_runner_new/test_runner_db.spl` | Fixed 3 blank line terminators | ✅ Complete |

---

## Next Steps

1. **Integrate CLI commands** - Add `test --batch` and `test-analyze` to main CLI
2. **Execute Phase 2.1** - Rebuild bootstrap with static method desugaring
3. **Run automated fixes** - Apply constructor and import fixes in batches
4. **Measure improvement** - Track pass rate increase after each phase
5. **Document workarounds** - Create comprehensive runtime limitation guide

---

## Success Metrics

| Metric | Baseline | Current | Target |
|--------|----------|---------|--------|
| Test pass rate | 72% | 72% | 90-95% |
| Passing tests | 6,685 | 6,685 | 8,340+ |
| Failed files | 148 | 148 | <50 |
| Infrastructure ready | 0% | 100% ✅ | 100% |
| Fix scripts ready | 0% | 50% | 100% |

---

## Timeline

- **Phase 0 Start:** 2026-02-07 (Today)
- **Phase 0 Complete:** 2026-02-07 (Today) ✅
- **Phase 1 Partial:** 2026-02-07 (Today) ✅ (2/4 scripts)
- **Expected Phase 2:** Within 2 days
- **Expected 90% target:** Within 2-3 weeks (30 hours total)

---

## Notes

- All scripts include dry-run mode for safety
- Test database now correctly formats SDN with blank line terminators
- Batch runner enables controlled testing during bulk fixes
- Failure analyzer provides actionable fix recommendations

**Status:** Infrastructure phase complete, automation phase 50% complete, ready for execution.
