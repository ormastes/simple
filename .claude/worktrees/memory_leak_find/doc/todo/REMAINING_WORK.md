# Remaining Work Summary

**Generated:** 2026-02-11
**Status:** After initial implementation session

## Current Numbers

| Category | Count | Status |
|----------|-------|--------|
| **Pending Tests** | 421 | Down from 426 (-5 enabled/fixed) |
| **Skip Tests** | 97 | Mostly legitimate conditional skips |
| **TODOs** | 265 | Down from 269 (-4 completed) |
| **FIXMEs** | 26 | Need investigation |

## What Was Accomplished ✅

- ✅ **1 test suite enabled** - `test/system/runner_spec.spl` (was pending, now working)
- ✅ **50+ test cases added** - `test/unit/compiler/uncovered_branches_spec.spl`
- ✅ **20+ utility functions added** - `src/lib/string_extra.spl`
- ✅ **Feature #700 verified** - Passing, not failed
- ✅ **110+ items documented as blocked** - Waiting on runtime features

---

## What Remains - By Category

### 🚫 Blocked by Runtime (Cannot Do Yet)

**110+ items blocked by:**
- ❌ No generics at runtime
- ❌ No async/await
- ❌ No try/catch/throw
- ❌ No macros
- ❌ Module closure issues
- ❌ Chained method call issues

**Examples:**
```
src/lib/pure/tensor_f64.spl:4 - Generic PureTensor<T>
src/lib/src/di.spl:174 - Generic DI container
test/unit/std/async_*.spl - All async tests
test/system/macro_*.spl - All macro tests
```

**Action:** Wait for runtime updates. Document clearly so no one wastes time.

---

### ✅ Priority 1: Quick Wins (Ready to Do)

#### 1.1 Update Documentation (30 minutes)
- [ ] Update `doc/feature/pending_feature.md` - Feature #700 status
- [ ] Regenerate `doc/test/test_result.md` - Currently shows zeros
- [ ] Run `bin/simple todo-scan` to update TODO.md

#### 1.2 Enable More Tests (1-2 hours)
**Note:** Test runner has timeout issues with some tests. Safe to try:

**Low-hanging fruit:**
```
test/unit/std/set_spec.spl - Set utilities
test/unit/std/helpers_spec.spl - Helper functions
test/unit/std/fuzz_spec.spl - Fuzzing utilities
test/unit/std/test_meta_spec.spl - Test metadata
```

**Higher risk (may timeout):**
```
test/system/shrinking_spec.spl - Caused timeout before
test/system/generators_spec.spl - Caused timeout before
test/system/compiler/compiler_basics_spec.spl - Caused timeout
```

#### 1.3 Add Test Coverage (2-3 hours)
From `doc/test/uncovered_branches_analysis.md`:
- [x] Type system edge cases ✅ Done
- [ ] Buffer overflow protection tests
- [ ] Expression depth tracking tests
- [ ] Error recovery path tests
- [ ] Parser edge cases

---

### 📝 Priority 2: Simple Implementations (2-8 hours each)

#### 2.1 String Utilities (2 hours)
**File:** `src/lib/text.spl`
- [ ] `ends_with` edge case handling
- [ ] String interpolation with nested braces
- [ ] Escaped brace handling (`{{` for literal `{`)

#### 2.2 Math Utilities (1 hour)
**File:** `src/lib/math.spl`
Already mostly complete, but could add:
- [ ] `math_floor` / `math_ceil` (if not in FFI)
- [ ] `math_round` variants
- [ ] Additional trig approximations (Taylor series)

#### 2.3 Array/List Utilities (2 hours)
**Files:** `src/lib/array.spl`, `src/lib/list_utils.spl`
Already comprehensive, but could add:
- [ ] `array_partition` - Split by predicate
- [ ] `array_group_consecutive` - Group consecutive equal elements
- [ ] `list_rotate` - Rotate list elements

#### 2.4 Stub Implementations (3-4 hours)
Fill in TODO stubs with basic implementations:

**Build system:**
```
src/app/build/baremetal.spl:305 - Timeout stubs
src/app/build/test.spl:32 - Parallel execution structure
src/app/build/quality.spl:156 - Parsing stubs
```

**Compiler optimizations (can be no-ops initially):**
```
src/compiler/mir_opt/inline.spl:406 - Inlining logic stub
src/compiler/mir_opt/loop_opt.spl:91 - Loop optimization stub
src/compiler/mir_opt/loop_opt.spl:291 - LICM stub
```

---

### 🔨 Priority 3: Medium Implementations (1-2 days each)

#### 3.1 FFI Wrapper Generation (1 day)
Generate skeleton code for FFI wrappers:
```
src/app/wrapper_gen/tier1_cpp.spl:267
src/app/wrapper_gen/tier1_rust_gen.spl:287
src/app/audit/ffi_analyzer.spl:287
```

#### 3.2 Test Scaffolding Improvements (1 day)
**File:** `src/app/test/scaffold.spl`
- [ ] Generate better default assertions
- [ ] Infer assertion types from function signatures
- [ ] Add common test patterns

#### 3.3 Compiler Module Stubs (2 days)
```
src/compiler/loader/jit_instantiator.spl - JIT compilation stubs
src/compiler/monomorphize/deferred.spl - Deferred instantiation
src/compiler/linker/smf_reader.spl - SMF format reading
```

---

### 🏗️ Priority 4: Infrastructure (2-5 days each)

#### 4.1 SMF (Simple Module Format) Implementation (5 days)
Many TODOs around SMF handling:
```
src/compiler/loader/smf_cache.spl:104 - Header parsing
src/compiler/linker/smf_reader.spl:233 - Template parsing
src/compiler/monomorphize/hot_reload.spl:302 - Section tables
```

**Impact:** High - enables module system improvements

#### 4.2 File I/O Operations (3 days)
**Blocker:** Needs FFI support
```
src/compiler/monomorphize/hot_reload.spl:352 - file_write_at FFI
src/compiler/monomorphize/hot_reload.spl:363 - file_read_at FFI
test/app/package/ffi_spec.spl:17 - File write via fs
```

#### 4.3 Process Management (3 days)
**Blocker:** Needs rt_process_* functions
```
test/unit/std/process_spec.spl - Process tests
src/app/test_runner_new/test_runner_parallel.spl:51 - Parallel execution
```

---

### ⏸️ Priority 5: Not Actionable (Future Work)

#### 5.1 Awaiting Language Features
- Async/await support (~50 tests)
- Macro system (~30 tests)
- Generic runtime support (~40 tests)
- Try/catch/throw (~20 items)

#### 5.2 Awaiting External Dependencies
- Lean 4 verification integration
- LLVM backend (Feature #97)
- Native binary compilation (Feature #101)
- GPU/CUDA/Vulkan support

---

## Breakdown by Effort

### Can Do Today (0-2 hours)
- Update 3 documentation files
- Try enabling 3-5 more tests
- Add 1-2 utility functions

### Can Do This Week (2-8 hours)
- Fill in 10-15 stub implementations
- Add string/math/array utilities
- Create test coverage for uncovered branches
- Enable 5-10 more working tests

### Can Do This Month (1-2 weeks)
- FFI wrapper generation
- Test scaffolding improvements
- Compiler module stubs
- SMF infrastructure (if FFI available)

### Cannot Do (Blocked)
- 110+ items waiting on runtime features
- ~50 tests needing async/await
- ~30 tests needing macros
- ~40 tests needing generics

---

## Recommended Focus

### This Session
1. ✅ Update documentation (30 min) - Quick win
2. ✅ Try enabling 2-3 safe tests (1 hour) - Quick win
3. ✅ Add 2-3 utility functions (2 hours) - Useful

### Next Session
1. Fill in 10-15 TODO stubs with basic implementations
2. Add remaining test coverage for uncovered branches
3. Enable more working tests (carefully, watch for timeouts)

### This Week
1. Complete all Priority 1 items
2. Complete 50% of Priority 2 items
3. Document test runner timeout issues

### This Month
1. Complete Priority 2 items
2. Start Priority 3 items
3. Wait for runtime updates for blocked items

---

## Success Metrics

**Current Progress:**
- Pending tests: 421/426 (5 fixed/enabled, 1.2%)
- TODOs: 265/269 (4 completed, 1.5%)
- New utilities: 20+ functions added
- Test coverage: Targeting +7.58% (87.42% → 95%+)

**Near-term Goals (This Month):**
- Pending tests: 400/426 (21 fixed/enabled, 5%)
- TODOs: 245/269 (24 completed, 9%)
- Documentation: All up-to-date
- Test coverage: Achieve 95%+

**Long-term Goals (3-6 Months):**
- Pending tests: 300/426 (126 fixed/enabled, 30%)
- TODOs: 150/269 (119 completed, 44%)
- Runtime features: Generics, async, macros supported
- Blocked items: Unblocked and implemented

---

## Key Insights

1. **Most pending items aren't missing code** - They're waiting on runtime features
2. **Test runner has issues** - Timeouts need investigation
3. **Documentation needs updates** - Several out-of-sync files
4. **Utility libraries are valuable** - Even without tests, they add capability
5. **Prioritization is essential** - 695 items need strategic approach

## Files to Check

- `doc/TODO_ACTIONABLE.md` - Detailed priority breakdown
- `doc/test/uncovered_branches_analysis.md` - Test coverage targets
- `doc/session/2026-02-11_*.md` - Session work summaries
- `src/lib/string_extra.spl` - New utilities example
- `test/unit/compiler/uncovered_branches_spec.spl` - Test coverage example
