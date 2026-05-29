# Remaining Test Opportunities Analysis (2026-02-08)

## Current Status

**Test Suite Overview:**
- **Total Tests:** 20,293
- **Skipped:** 1,142 (5.6%)
- **Slow Tests:** 141
- **Phases 1-3 Fixed:** 229 tests

---

## Completed Phases

| Phase | Focus | Tests | Status |
|-------|-------|-------|--------|
| 1c | Concurrent module | 33 | ✅ Complete |
| 2a | Debug module | 98 | ✅ Complete |
| 2b | Database resources | 23 | ✅ Complete |
| 3a | TreeSitter lexer | 42 | ✅ Complete |
| 3b | Failsafe | 32 | ✅ Complete |
| 3c | Table | 1 | ⚠️ Limited |
| 4 | SFFI (design) | 0 | 📋 Plan Ready |
| **Total** | | **229** | **✅ Done** |

---

## Potential Phase 5+: Additional Opportunities

### Category Analysis

Based on test file names, remaining opportunities include:

#### A. Language Features (Compiler/Runtime)
**Requires compiler/runtime work - NOT fixable with Simple code**
- Suspension operators (24 tests)
- Custom blocks (48 tests)
- Async/await effects
- Generator state machines
- GPU kernels
- Handle pointers
- Borrowing system

**Effort:** N/A (out of scope for Pure Simple fixes)

#### B. Standard Library Modules
**Potentially fixable with Pure Simple code**

Candidates from skipped tests:
1. **Config/Environment** - config_env_spec.spl
2. **Context Blocks** - context_blocks_spec.spl
3. **Functional Updates** - functional_update_spec.spl
4. **Dictionary Operations** - dictionary_types_spec.spl
5. **Array Operations** - array_types_spec.spl

**Estimated:** 50-100 tests
**Effort:** 2-4 days

#### C. CLI/Tooling Tests
**Fixable with CLI improvements**

From file list:
1. **CLI Dispatch** - cli_dispatch_spec (18/25 remaining)
2. **Watcher App** - watcher_basics_spec, watcher_app_spec
3. **Compiler Basics** - compiler_basics_spec

**Estimated:** 30-50 tests
**Effort:** 1-2 days

#### D. Integration Tests
**May be fixable depending on dependencies**

Categories:
1. **MCP Extended** - coordinator_extended_spec
2. **Test Database** - test_db_integrity_spec
3. **E2E Scenarios** - Various integration specs

**Estimated:** 20-40 tests
**Effort:** 1-3 days

---

## Recommended Phase 5: Quick Wins Round 2

### Phase 5a: CLI Dispatch Completion (18 tests, 2 hours)

**File:** `test/integration/cli_dispatch_spec.spl`

**Status:** 7/25 passing (18 remain)

**Blocker:** Module closure limitation (from Phase 1a)
- Functions can't access module-level collections dynamically
- COMMAND_TABLE can't be queried from exported functions

**Possible Fix:**
1. Pre-compute more helper data at module init
2. Export command list as static data
3. Use workarounds similar to Phase 2a (debug module)

**Effort:** 2-4 hours

### Phase 5b: Simple Standard Library Extensions (50-80 tests, 2-3 days)

**Target:** Tests that need small utility modules

Candidates:
1. **Array utilities** (array_types_spec) - ~15 tests
   - Missing: advanced slicing, transformations
   - Solution: Add helper functions to std.array

2. **Dictionary utilities** (dictionary_types_spec) - ~20 tests
   - Missing: merge, deep copy, path access
   - Solution: Create std.dict module

3. **Config/Environment** (config_env_spec) - ~15 tests
   - Missing: Config file parsing
   - Solution: Use existing std.sdn module

4. **Context utilities** (context_blocks_spec) - ~10 tests
   - Missing: Context managers
   - Solution: Create std.context module

5. **Functional utilities** (functional_update_spec) - ~10 tests
   - Missing: Immutable update helpers
   - Solution: Add to std.functional

**Effort:** 2-3 days to implement modules + convert tests

### Phase 5c: Low-Hanging Fruit Hunt (20-30 tests, 1 day)

**Approach:** Find tests that are skipped due to simple issues

Common fixable patterns:
- Import path errors
- Missing helper functions
- Outdated API calls
- Simple stub implementations

**Method:**
1. Run test suite with detailed output
2. Grep for common error patterns
3. Fix batch of similar issues
4. Re-run and iterate

**Effort:** 1 day of systematic fixes

---

## Phase Comparison

| Phase | Tests | Effort | Type | Priority |
|-------|-------|--------|------|----------|
| **Completed: 1-3** | 229 | 6h | ✅ Done | - |
| **Design: 4** | 0 (79 planned) | 5-7d | 📋 Plan | Medium |
| **5a: CLI Completion** | 18 | 2-4h | Module fixes | High |
| **5b: Stdlib Extensions** | 50-80 | 2-3d | New modules | High |
| **5c: Quick Wins** | 20-30 | 1d | Bug fixes | High |
| **Total Phase 5** | **88-128** | **3-5 days** | | |

---

## Effort vs Impact Analysis

### High Impact, Low Effort ✅
- **Phase 5a (CLI):** 18 tests in 2-4 hours
- **Phase 5c (Quick Wins):** 20-30 tests in 1 day

### High Impact, Medium Effort ⚠️
- **Phase 5b (Stdlib):** 50-80 tests in 2-3 days
- **Phase 4 (SFFI):** 79 tests in 5-7 days

### Lower Priority
- **Compiler features:** Requires deep runtime work
- **GPU/Graphics:** Specialized domains
- **Async/Generators:** Complex runtime features

---

## Recommended Next Steps

### Option 1: Continue Test Fixes (Phase 5)
**Timeline:** 3-5 days
**Result:** 88-128 additional tests passing
**Total Impact:** 229 + 128 = **357 tests fixed**

**Phases:**
1. Day 1: Phase 5a (CLI) + Phase 5c start (Quick wins)
2. Day 2-3: Phase 5c (continue Quick wins)
3. Day 4-5: Phase 5b (Stdlib extensions)

### Option 2: Implement SFFI (Phase 4)
**Timeline:** 5-7 days
**Result:** 79 tests passing (regex + http + others)
**Requires:** Runtime modifications

### Option 3: Hybrid Approach
**Timeline:** 5-7 days
**Result:** Maximum tests fixed

**Week 1:**
- Days 1-2: Phase 5a + 5c (38-48 tests)
- Days 3-4: Phase 5b partial (30-40 tests)
- Days 5-7: Phase 4 (SFFI regex + http, 45 tests)

**Total:** 113-133 additional tests

---

## Test Categories NOT Fixable with Simple Code

These require compiler/runtime changes:

### Compiler Features
- Suspension operators (`~` syntax)
- Custom block syntax (try/catch/finally)
- Trait system
- Advanced type inference
- Macro system

**Tests:** ~500-1000
**Effort:** Months (outside scope)

### Runtime Features
- Async/await with proper suspensions
- Generator state machines
- Borrowing/ownership system
- GPU kernel compilation
- Handle pointer system

**Tests:** ~300-500
**Effort:** Weeks to months

### JIT/Compiler-Only
- Compiled-only test mode
- Optimization passes
- Code generation variants

**Tests:** ~100-200
**Effort:** Requires JIT work

---

## Conclusion

**Yes, Phase 5+ exists!**

**Immediate Opportunities:**
- Phase 5a: CLI completion (18 tests, 2-4 hours)
- Phase 5b: Stdlib extensions (50-80 tests, 2-3 days)
- Phase 5c: Quick wins (20-30 tests, 1 day)

**Total Potential:** 88-128 tests in 3-5 days

**Beyond Phase 5:**
- Phase 4: SFFI (79 tests, 5-7 days) when runtime work begins
- Additional stdlib modules as needs arise
- Ongoing quick wins from test suite analysis

**Estimated ceiling for Simple-only fixes:** ~500-600 tests total
- Phases 1-3: 229 done ✅
- Phase 4: 79 possible (needs runtime)
- Phase 5: 88-128 likely
- Future: 100-200 additional opportunities

**Remaining ~19,500 tests** require compiler/runtime features beyond Pure Simple code.

---

## Recommendation

**Start Phase 5a immediately** - Highest ROI (18 tests in 2-4 hours).

Then evaluate:
- If quick wins continue → Phase 5c
- If want bigger impact → Phase 5b
- If ready for challenge → Phase 4 (SFFI)

**All three phases are valuable and ready to execute!**
