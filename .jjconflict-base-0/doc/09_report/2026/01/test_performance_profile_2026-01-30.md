# Test Performance Profiling Report

**Generated:** 2026-01-30
**Total Test Runtime:** 172.5 seconds (2.87 minutes)
**Total Tests:** 7,810
**Average Test Time:** 22ms per test

---

## Executive Summary

Profiling identified **8 slow test files** consuming **~29 seconds** (17% of total runtime) and **1 hanging test** consuming 120 seconds (70% of total runtime).

**Quick Wins:**
- Fix 1 hanging test → Save 120 seconds (70% reduction)
- Optimize 1 critical slow test → Save ~16 seconds (9% reduction)
- **Total potential savings: ~136 seconds → Runtime down to 36 seconds**

---

## Slow Test Files (>1 second)

| Rank | Test File | Time (ms) | Tests | Avg/Test | Category |
|------|-----------|-----------|-------|----------|----------|
| 🔴 1 | test_analysis_spec.spl | **16,619** | 56 | 297ms | App/CLI |
| 🟡 2 | symbol_table_spec.spl | **3,958** | 27 | 147ms | MCP |
| 🟡 3 | mcp_spec.spl | **1,996** | ? | ?ms | MCP |
| 🟡 4 | regex_spec.spl | **1,578** | ? | ?ms | Core |
| 🟡 5 | transport_edge_cases_spec.spl | **1,469** | ? | ?ms | MCP |
| 🟡 6 | failure_analysis_spec.spl | **1,421** | ? | ?ms | MCP |
| 🟡 7 | dependencies_spec.spl | **1,364** | ? | ?ms | MCP |

**Total slow test time:** ~28.4 seconds (16.5% of runtime)

---

## Hanging Tests (>120 seconds)

| Test File | Timeout | Status | Impact |
|-----------|---------|--------|--------|
| 🚫 **async_features_spec.spl** | **120s** | Timed out | **70% of runtime** |

**Root Cause:** Unknown - likely infinite loop or blocking async operation

---

## Performance Analysis by Category

### 1. test_analysis_spec.spl - 16.6 seconds 🔴 CRITICAL

**Profile:**
- 56 tests in 16.6 seconds
- Average: 297ms per test
- 10x slower than normal (30ms expected)

**What it tests:**
- CLI tool for analyzing test failures
- Error classification (parse/semantic/timeout)
- Feature extraction from error messages
- SDN file I/O operations

**Bottleneck Analysis:**
- ❌ Not I/O bound (only 4 file operations in entire suite)
- ❌ Not algorithmic (simple string matching)
- ✅ **Likely:** Interpreter overhead + module loading

**Recommended Fixes:**

1. **Quick Fix:** Mark as `slow_it` to exclude from quick test runs
   - Effort: 5 minutes
   - Savings: 16.6 seconds during development cycles

2. **Medium Fix:** Cache module imports between tests
   - Effort: 2-4 hours
   - Savings: ~8 seconds (50% reduction)

3. **Long-term Fix:** Compile critical test suites instead of interpreting
   - Effort: 1 week (build system changes)
   - Savings: ~13 seconds (80% reduction)

---

### 2. MCP Tests - 10.2 seconds 🟡 MODERATE

**Affected Files:**
- symbol_table_spec.spl (4.0s, 27 tests, 148ms avg)
- mcp_spec.spl (2.0s)
- transport_edge_cases_spec.spl (1.5s)
- failure_analysis_spec.spl (1.4s)
- dependencies_spec.spl (1.4s)

**Profile:**
- ~10 seconds total for MCP category
- Average: 100-150ms per test
- 3-5x slower than normal

**What they test:**
- Model Context Protocol implementation
- Symbol tables and cross-references
- Transport layer edge cases
- Dependency analysis

**Bottleneck Analysis:**
- Likely: Complex data structure operations
- Possible: Repeated setup without caching

**Recommended Fixes:**

1. **Quick Fix:** Mark slowest MCP tests as `slow_it`
   - Effort: 10 minutes
   - Savings: 10 seconds during development

2. **Medium Fix:** Add `before_all` setup to share data structures
   - Effort: 3-5 hours
   - Savings: ~5 seconds (50% reduction)

3. **Long-term Fix:** Optimize symbol table lookups (hash maps)
   - Effort: 1-2 days
   - Savings: ~7 seconds (70% reduction)

---

### 3. regex_spec.spl - 1.6 seconds 🟡 MODERATE

**Profile:**
- 1.6 seconds total
- Likely testing regex engine

**Bottleneck Analysis:**
- Regex compilation/matching is inherently expensive
- Possibly testing complex patterns or large inputs

**Recommended Fixes:**

1. **Quick Fix:** Mark as `slow_it` if testing performance edge cases
   - Effort: 2 minutes
   - Savings: 1.6 seconds during development

2. **Medium Fix:** Cache compiled regexes
   - Effort: 1-2 hours
   - Savings: ~0.8 seconds (50% reduction)

---

### 4. async_features_spec.spl - 120s TIMEOUT 🚫 CRITICAL

**Profile:**
- 42 tests, times out at 120 seconds
- **70% of total test runtime wasted**

**What it tests:**
- Lambda expressions
- Future creation and await
- Async functions
- Generators and yield

**Root Cause Investigation Required:**

**Hypothesis 1: Deadlock in async runtime**
- Future never resolves
- Await blocks forever
- **Action:** Add debug logging to async runtime

**Hypothesis 2: Infinite loop in generator**
- Generator yield loop never terminates
- **Action:** Review generator tests for termination conditions

**Hypothesis 3: Test framework timeout not working**
- Individual test hangs but timeout doesn't trigger
- **Action:** Verify test timeout mechanism

**Recommended Fixes:**

1. **Immediate Fix:** Run test with increased logging to identify hanging test
   - Effort: 30 minutes
   - Command: `./target/debug/simple_old test async_features_spec.spl --debug 2>&1 | tee debug.log`

2. **Short-term Fix:** Add individual test timeouts (30s max per test)
   - Effort: 2-3 hours
   - Savings: 90 seconds (test would fail fast at 30s instead of 120s)

3. **Root Fix:** Debug and fix the hanging async operation
   - Effort: 4-8 hours (depends on complexity)
   - Savings: 120 seconds (test completes normally)

---

## Root Cause Summary

### Interpreter Overhead (Primary)

**Evidence:**
- test_analysis_spec.spl: 297ms/test for simple string operations
- symbol_table_spec.spl: 148ms/test for data structure operations
- Normal tests: ~20-30ms/test

**Conclusion:**
Running in interpreter mode adds 100-270ms overhead per test.

**Solutions:**
1. Compile hot test paths
2. Cache module imports
3. Reduce test setup/teardown overhead

### Missing Caching (Secondary)

**Evidence:**
- MCP tests likely rebuild symbol tables for each test
- No `before_all` setup observed

**Solutions:**
1. Add `before_all` for expensive setup
2. Share data structures across tests
3. Memoize expensive computations

### Hanging Tests (Critical)

**Evidence:**
- async_features_spec.spl times out at 120s
- 70% of runtime wasted

**Solutions:**
1. Debug async runtime
2. Add per-test timeouts
3. Fix infinite loop/deadlock

---

## Recommended Action Plan

### Phase 1: Immediate Wins (1 hour)

**Task:** Mark slow tests with `slow_it` to exclude from quick runs

**Files to modify:**
```simple
# test_analysis_spec.spl - change 56 tests
slow_it "basic lambda with single param": ...

# MCP tests - change ~50 tests total
slow_it "creates empty symbol table": ...
```

**Expected Outcome:**
- Quick test runs: 172s → 36s (79% faster)
- Slow test runs: Same as before (run with `--only-slow`)

**Effort:** 1 hour (mechanical changes)

---

### Phase 2: Fix Hanging Test (4 hours)

**Task:** Debug and fix async_features_spec.spl timeout

**Steps:**
1. Run with debug logging to identify hanging test (30 min)
2. Isolate the specific test that hangs (30 min)
3. Review async/future implementation for deadlock (2 hours)
4. Fix the bug (1 hour)
5. Verify fix (30 min)

**Expected Outcome:**
- Test completes in <5 seconds instead of timing out
- Savings: 115 seconds per test run

**Effort:** 4 hours

---

### Phase 3: Add Test Caching (1 day)

**Task:** Reduce MCP test overhead with shared setup

**Changes:**
```simple
describe "SymbolTable":
    before_all:
        # Create shared test data once
        val shared_table = create_large_symbol_table()
        val shared_refs = create_reference_graph()

    it "gets symbol by name":
        # Use shared_table instead of creating new one
        val result = shared_table.get("module.func")
        expect result.is_some()
```

**Expected Outcome:**
- MCP tests: 10s → 5s (50% reduction)
- Total runtime: 36s → 31s

**Effort:** 1 day

---

### Phase 4: Optimize Hot Paths (1 week)

**Task:** Compile critical test suites or optimize interpreter

**Options:**
1. Pre-compile test framework (4-5 days)
2. Add JIT for hot interpreter paths (1 week)
3. Optimize interpreter dispatch (2-3 days)

**Expected Outcome:**
- test_analysis_spec: 16.6s → 3-5s (70-80% reduction)
- Total runtime: 31s → 20s

**Effort:** 1 week

---

## Expected Progress

| Phase | Duration | Action | Runtime | Savings |
|-------|----------|--------|---------|---------|
| Current | - | - | 172.5s | - |
| Phase 1 | 1 hour | Mark slow tests | 36s (quick mode) | **79%** |
| Phase 2 | 4 hours | Fix hanging test | 21s | **88%** |
| Phase 3 | 1 day | Add caching | 16s | **91%** |
| Phase 4 | 1 week | Optimize interpreter | 10-12s | **93-94%** |

---

## Metrics Summary

### Current State
- **Total runtime:** 172.5 seconds
- **Slow tests (>1s):** 7 files, 28.4 seconds (16.5%)
- **Hanging tests:** 1 file, 120 seconds (70%)
- **Normal tests:** ~24 seconds (14%)

### After All Fixes
- **Total runtime:** 10-12 seconds
- **Slow tests:** 0
- **Hanging tests:** 0
- **Speed improvement:** 93-94% faster

---

## Deferred Optimizations

These optimizations have lower ROI and can be deferred:

1. **Regex test optimization** - Only 1.6s, acceptable for comprehensive regex testing
2. **Individual test micro-optimizations** - Diminishing returns below 100ms/test
3. **Test parallelization** - Complex, requires thread-safe test framework

---

## Conclusion

**Current Situation:**
- ✅ Tests run successfully (90.5% pass rate)
- ⚠️ Runtime is 10x slower than ideal due to interpreter overhead
- 🚫 1 critical hanging test wastes 70% of runtime

**Recommended Priority:**
1. **P0:** Fix hanging test (4 hours, 88% savings)
2. **P1:** Mark slow tests (1 hour, 79% quick-run savings)
3. **P2:** Add test caching (1 day, 91% total savings)
4. **P3:** Optimize interpreter (1 week, 93% total savings)

**3-Day Plan:**
- Day 1: Phase 1 + Phase 2 (fix hanging + mark slow)
- Day 2: Phase 3 (add caching)
- Day 3: Testing and verification

**Total Effort:** 2-3 days
**Total Savings:** 91% faster (172s → 16s)

---

**Generated:** 2026-01-30
**Next Steps:** Execute Phase 1 (mark slow tests) and Phase 2 (fix hanging test)
