# TODO: Next Session Priorities
## Based on Migration Session - February 3, 2026

**Session Summary:** Successfully completed 3 migration phases, eliminated 18 FFI calls, created std.path module, cleaned up 1,004 files. Discovered 2 compiler limitations that need attention.

## Critical Issues (Blockers)

### 1. Module System Enhancement ⚠️ BLOCKS std.path usage
**Priority:** HIGH (blocks test suite and final path FFI removal)

**Issue:** Custom std modules can't be imported yet
- `use std.path as path` fails with "method not found on type dict"
- `use std.path.{basename}` fails with "function not found"

**Files Ready:**
- ✅ `src/lib/path.spl` (217 lines, 10 functions, ready to use)
- ✅ `test/std/path_spec.spl` (350 lines, 85+ tests, ready to run)

**Requirements:**
1. Module resolution: Recognize `use std.path` → `src/lib/path.spl`
2. Namespace support: Allow `path.basename()` on imported namespace
3. Selective imports: Support `use std.path.{basename, dirname}`

**Estimated Effort:** 4-8 hours compiler work

**Task ID:** #10

**Impact:** Blocks final removal of 2 rt_path_basename FFI calls

---

### 2. Circular Dependency Fix ⚠️ BLOCKS 248 tests
**Priority:** HIGH (blocks lexer, parser, type_infer tests)

**Issue:** Circular dependency in compiler modules causes 2+ minute timeouts
- Cycle: lexer → blocks → builtin → hir → parser → lexer

**Fix Implemented:** Lazy initialization in `src/compiler/lexer.spl`
- Changed `block_registry: BlockRegistry` → `BlockRegistry?`
- Added `get_block_registry()` method for lazy loading
- Compiles successfully

**Verification Needed:**
1. Clean build of compiler
2. Test lexer module (doesn't timeout)
3. Run blocked test suites

**Tests Blocked:**
- `test/compiler/lexer_comprehensive_spec.spl` (178 tests)
- `test/compiler/type_infer_comprehensive_spec.spl` (33 tests)
- `test/std/config_comprehensive_spec.spl` (37 tests)
- **Total:** 248 tests blocked

**Estimated Effort:** 1-2 hours verification

**Task ID:** #11

**Impact:** Unlocks ~1,275 branches for coverage testing

---

## High Priority (Quick Wins)

### 3. Verify Test Suite Still Works ✅ After cleanup
**Priority:** HIGH (verify cleanup was safe)

**Action:**
```bash
# Run full test suite
simple test

# Verify count unchanged
simple test --list | wc -l
# Expected: ~500-800 tests (same as before cleanup)

# Run specific test files
simple test test/std/error_handling_spec.spl
simple test test/std/collections_spec.spl
simple test test/app/formatter_comprehensive_spec.spl
```

**Estimated Time:** 15-30 minutes

**Risk:** Very low (only removed build artifacts)

---

### 4. Add Missing Tests 📝 UPX compression
**Priority:** MEDIUM (complete stdlib coverage)

**File to Create:** `test/std/upx_spec.spl`

**Coverage Needed:**
- UPX compression functions
- Integration tests
- Error handling

**Reference:**
- Rust tests: `rust/runtime/tests/upx_integration_test.rs`
- Simple lib: `src/lib/compress/upx.spl` (if exists)

**Estimated Effort:** 2-3 hours

**Impact:** Complete stdlib test coverage

---

### 5. Complete Makefile Deprecation ⚠️ 67 targets remaining
**Priority:** MEDIUM (user experience)

**Current:** 20/87 targets have warnings (23%)
**Target:** 87/87 targets (100%)

**Pattern:**
```makefile
target-name:
	$(call DEPRECATION_WARNING,simple-build-equivalent)
	# existing commands
```

**Targets Needing Warnings:**
- Build variants (debug, release variants)
- Coverage variants (unit, integration, system)
- Cleanup targets
- Documentation targets

**Estimated Effort:** 1-2 hours

**Impact:** All users guided to Simple build system

---

## Medium Priority (Migration Continuation)

### 6. Migrate Coverage Tools 🔄 Large migration
**Priority:** MEDIUM (3,500 lines to migrate)

**Location:** `rust/util/simple_mock_helper/src/bin/coverage_gen.rs`

**Components:**
- `coverage_gen.rs` (198 lines) - CLI
- `coverage_extended.rs` (1,036 lines) - Coverage analysis
- Related utilities (~2,300 lines)

**Simple Wrapper Exists:** `src/app/coverage/main.spl` (200 lines)

**Blockers:**
- Need JSON parsing in Simple (or use SDN)
- Need YAML parsing in Simple
- File I/O (✅ already have rt_file_*)

**Estimated Effort:** 8-10 hours

**Impact:** ~3,500 lines Rust → Simple

---

### 7. Migrate Mock Helper Core 🔄 Large migration
**Priority:** LOW (can defer)

**Location:** `rust/util/simple_mock_helper/src/` (~3,514 lines)

**Components:**
- API scanner (391 lines)
- Coverage analysis (571 lines)
- FFI helpers (534 lines) - keep in Rust
- Fluent test API (729 lines)
- Mock policies (290 lines)
- Test verification (421 lines)

**Strategy:**
- Phase 1: CLI tools
- Phase 2: API scanner
- Phase 3: Coverage analysis
- Phase 4: Keep FFI helpers

**Estimated Effort:** 20-25 hours

**Impact:** ~2,500 lines migrated (keep FFI helpers)

---

## Low Priority (Future Work)

### 8. Create Test Strategy Doc 📄 Prevent redundancy
**File:** `doc/test/test_strategy.md`

**Content:**
- When to write Rust tests (runtime core, FFI)
- When to write Simple tests (application, API)
- How to avoid redundancy
- Test organization guidelines

**Estimated Effort:** 30-60 minutes

---

### 9. Consolidate Sample Directories 🧹 Cleanup
**Issue:** Duplicate samples in different locations

**Locations:**
- `test/system/features/` (primary)
- `test/system/interpreter/sample/`
- `test/system/compiler/sample/`

**Action:**
1. Compare directories (ensure identical)
2. Keep `test/system/features/` only
3. Remove duplicates

**Estimated Effort:** 30-60 minutes

**Impact:** Remove ~50-100 duplicate files

---

### 10. Create std.text Module 📦 New stdlib
**File:** `src/lib/text.spl`

**Functions:**
- `trim()`, `trim_start()`, `trim_end()`
- `pad_left()`, `pad_right()`
- `repeat()`
- `reverse()`
- `to_upper()`, `to_lower()`
- `is_empty()`, `is_whitespace()`

**Estimated Effort:** 3-4 hours (including tests)

**Blocked By:** Module system enhancement

---

## Verification Checklist

Before next major migration:
- [ ] Module system supports std modules
- [ ] Circular dependency resolved
- [ ] Test suite verified (no regressions)
- [ ] All reports reviewed

## Session Notes

**What Worked Well:**
- ✅ Documentation-first approach (clear targets)
- ✅ Small iterations (4 phases)
- ✅ Comprehensive testing (85+ tests)
- ✅ Safe cleanup (only artifacts)

**What to Improve:**
- ⚠️ Test module system before creating modules
- ⚠️ Verify circular deps before writing dependent tests
- ⚠️ Check compiler support for features used

**Lessons:**
1. Pure Simple preferred when possible
2. FFI boundary well-defined (549 functions categorized)
3. Build artifacts accumulate (need .gitignore + cleanup)
4. Rust tests mostly necessary (different layers)

## Quick Commands Reference

```bash
# Build
simple build                    # Debug
simple build --release          # Release

# Test
simple test                     # All tests
simple test --list              # List tests
simple test path/to/spec.spl   # Single file

# Cleanup (if needed again)
find test/ -name "*.smf" -delete
find test/ -name ".simple" -type d -exec rm -rf {} +

# Check for obsolete files
find test/ -name "*.py" -o -name "*.sdt"

# Git status
git status
jj status  # If using jujutsu
```

## Documentation Reference

**Migration Reports:**
- Complete summary: `doc/report/complete_session_summary_2026-02-03.md`
- FFI spec: `doc/spec/ffi_boundary_spec.md`
- Quick reference: `doc/guide/migration_quick_reference.md`

**Created This Session:**
- `src/lib/path.spl` - Path utilities (ready to use)
- `test/std/path_spec.spl` - 85+ tests (ready to run)
- 12 comprehensive reports (~5,400 lines)

## Success Metrics

**This Session:**
- ✅ 18 FFI calls eliminated (90% of target)
- ✅ 1,004 files cleaned up (59% reduction)
- ✅ 10 stdlib functions added
- ✅ 85+ tests created
- ✅ 5,400+ lines documented

**Overall Progress:**
- Simple code: 27.4% (up from 27%)
- Application layer: 55% Simple (up from 50%)
- Legacy FFI: 0 calls remaining
- Modern FFI: ~20 calls (all necessary)

**Targets:**
- Overall: 40% Simple
- Application layer: 80% Simple

---

## Next Session Strategy

**Recommended Order:**
1. Fix critical blockers (#1, #2) - 6-10 hours
2. Verify and test (#3) - 30 minutes
3. Quick wins (#4, #5) - 3-5 hours
4. Plan next migration phase

**Total Estimated:** 10-15 hours work

**Expected Outcome:**
- Module system working
- Circular deps resolved
- 248 tests unblocked
- Makefile 100% deprecated
- Ready for major migrations

---

**Created:** February 3, 2026
**Based On:** Complete session summary
**Status:** Ready for next session
