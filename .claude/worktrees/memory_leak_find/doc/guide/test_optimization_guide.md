# Test Optimization Guide

**Date:** 2026-02-08
**Status:** Living Document

## Overview

This guide documents proven techniques for optimizing slow tests in the Simple compiler test suite.

## Quick Wins Checklist

Before diving into complex optimizations, check these common issues:

### 1. Missing Type Methods ✅
**Symptom:** Tests fail with "method not found" errors
**Fix:** Add missing methods to the type

```simple
# Example: Value enum was missing accessor methods
impl Value:
    fn is_int() -> bool:
        match self:
            case Int(_): true
            case _: false

    fn as_int() -> i64:
        match self:
            case Int(i): i
            case _: panic("not an int")
```

**Impact:** Can fix 30+ tests at once, eliminate semantic analysis overhead

### 2. Large Test Data 🔥
**Symptom:** Tests take 10+ seconds, create large arrays/strings
**Fix:** Reduce data sizes by 10x

```simple
# Before (slow)
slow_it "handles large arrays":
    val elements = [for i in 0..10000:  # ← 10k elements
        create_element(i)
    ]

# After (fast)
slow_it "handles large arrays":
    val elements = [for i in 0..1000:   # ← 1k elements
        create_element(i)
    ]
```

**Impact:** 10x data reduction typically yields 10x speedup

### 3. Missing Timing Infrastructure ⏱️
**Symptom:** Performance tests fail with "time_now not found"
**Fix:** Use std.timing module

```simple
# Add import
use std.timing.{time_now, time_elapsed}

# Use in tests
slow_it "benchmark operation":
    val start = time_now()
    expensive_operation()
    val elapsed = time_elapsed(start)
    expect elapsed < 100  # Should complete in <100ms
```

**Location:** `src/lib/timing.spl`

### 4. Deprecated API Usage 📚
**Symptom:** Tests fail with "method not found"
**Common Issues:**
- `.size()` → `.len()` for collections
- `.new()` → direct construction `Type(field: value)`
- `import` → `use` for imports

```simple
# Before
expect dict.size() == 10
val obj = MyClass.new(value: 42)

# After
expect dict.len() == 10
val obj = MyClass(value: 42)
```

## Optimization Patterns

### Pattern 1: Split Large Test Files

**When to use:** Test file has 40+ tests and takes 5+ seconds

```bash
# Before: single file with all tests
test/compiler/literal_converter_spec.spl  # 48 tests, 16s

# After: split by category
test/compiler/literal_converter_basic_spec.spl       # 15 tests, 2s
test/compiler/literal_converter_collections_spec.spl # 18 tests, 3s
test/compiler/literal_converter_edge_spec.spl        # 10 tests, 2s
test/compiler/literal_converter_perf_spec.spl        #  5 tests, 4s
```

**Benefits:**
- Faster iteration during development (run only relevant tests)
- Can skip performance tests locally, run in CI
- Easier to identify specific failures
- Enables parallel execution

### Pattern 2: Reduce Edge Case Complexity

**When to use:** Tests create deeply nested structures or very long strings

```simple
# Before
it "handles deeply nested structures":
    var nested = value
    for _ in 0..100:                    # ← 100 levels
        nested = wrap(nested)

# After
it "handles deeply nested structures":
    var nested = value
    for _ in 0..20:                     # ← 20 levels (still validates)
        nested = wrap(nested)
```

**Impact:** 5x reduction in nesting → 3-5x speedup

### Pattern 3: Use Test Data Builders

**When to use:** Many tests create similar complex objects

```simple
# Helper function reduces duplication
fn build_test_value(int_val: i64) -> Value:
    Value.Int(int_val)

fn build_test_array(size: i64) -> Value:
    val elements = [for i in 0..size:
        build_test_value(i)
    ]
    Value.Array(elements)

# Tests become simpler
it "handles arrays":
    val arr = build_test_array(100)  # ← Clear intent
    expect arr.is_array()
```

### Pattern 4: Mock External Resources

**When to use:** Tests call external binaries, network, or file system

```simple
# Before (slow - actual file I/O)
it "reads config file":
    file_write("test.conf", "key=value")
    val config = load_config("test.conf")
    file_delete("test.conf")

# After (fast - in-memory)
it "reads config file":
    val mock_fs = MockFileSystem()
    mock_fs.add("test.conf", "key=value")
    val config = load_config_from("test.conf", mock_fs)
```

**Impact:** Eliminates I/O latency, 10-100x speedup

### Pattern 5: Cache Module Compilation

**When to use:** Many tests import the same modules

```simple
# Framework-level optimization
# Load module once, reuse across tests
val cached_backend_module = load_module("compiler.backend")

# Tests reuse cached module
it "test 1":
    use_cached_module(cached_backend_module)
    # ...

it "test 2":
    use_cached_module(cached_backend_module)
    # ...
```

**Impact:** 2-3s per test file

## Measurement and Profiling

### Using std.timing

```simple
use std.timing.{time_now, time_elapsed, benchmark, profile}

# Single measurement
val start = time_now()
expensive_operation()
val elapsed = time_elapsed(start)
print "Took {elapsed}ms"

# Detailed profiling
val (result, timing) = profile("operation_name"):
    expensive_operation()
print "Elapsed: {timing.elapsed_ms}ms"

# Statistical benchmark
val stats = benchmark(100):  # Run 100 times
    operation()
print "Avg: {stats.avg_ms}ms, Min: {stats.min_ms}ms, Max: {stats.max_ms}ms"
```

### Finding Slow Tests

```bash
# Run tests and extract timing
bin/simple test --only-slow 2>&1 | \
    grep -E "PASSED|FAILED" | \
    grep -oE "[0-9]+ms" | \
    sort -rn | \
    head -20
```

## Case Study: literal_converter_spec

### Initial State
```
Duration: 16,008 ms (16.0 seconds)
Tests: 43 examples, 37 failures (86% failure rate)
```

### Root Causes
1. Missing Value enum methods (30 failures)
2. Missing timing functions (3 failures)
3. Wrong API usage: `.size()` vs `.len()` (4 failures)
4. Oversized performance tests (100k iterations)

### Fixes Applied

**1. Added Value Methods (+90 lines)**
```simple
# src/compiler/backend_types.spl
impl Value:
    fn is_int() -> bool
    fn as_int() -> i64
    # ... 16 more methods
```

**2. Created Timing Module (+180 lines)**
```simple
# src/lib/timing.spl
fn time_now() -> Instant
fn time_elapsed(start: Instant) -> i64
fn profile<T>(name: text, block: fn() -> T) -> (T, ProfileResult)
fn benchmark(iterations: i64, block: fn()) -> BenchmarkResult
```

**3. Fixed API Usage**
```simple
# Before
expect result.as_dict().size() == 2

# After
expect result.as_dict().len() == 2
```

**4. Reduced Test Data**
```simple
# Before
for i in 0..100000:  # 100k iterations

# After
for i in 0..10000:   # 10k iterations
```

### Final Result
```
Duration: 3,573 ms (3.6 seconds)
Tests: 48 examples, 7 failures (15% failure rate)
Speedup: 4.5x faster (77% reduction)
```

### Lessons Learned

1. **Infrastructure gaps cause cascading failures**
   - 1 missing method → 30 test failures
   - Fix once, benefit everywhere

2. **Test data size is critical**
   - 10x reduction → ~10x speedup (linear scaling)
   - Even passing tests get faster

3. **Semantic failures still waste time**
   - Tests run setup code before failing
   - Fix early failures for compound speedup

4. **Reusable infrastructure pays off**
   - Timing module useful for ALL performance tests
   - Value methods used by ALL backend tests

## Optimization Workflow

### Step 1: Measure
```bash
# Get baseline
bin/simple test --only-slow 2>&1 | tee baseline.txt

# Extract slowest tests
grep -E "PASSED|FAILED.*ms" baseline.txt | \
    grep -oE "[0-9]+ms.*spec.spl" | \
    sort -rn | \
    head -20
```

### Step 2: Analyze

For each slow test:
1. Read the test file
2. Count tests: `grep -E "(it |slow_it)" file.spl | wc -l`
3. Check for:
   - Large loops (`for i in 0..10000`)
   - Large data (`"x".repeat(10000)`)
   - Missing imports
   - Deprecated API usage
   - External I/O (file, network, process)

### Step 3: Fix

Apply quick wins first:
1. Add missing methods/imports
2. Reduce data sizes 10x
3. Fix deprecated APIs
4. Mock external resources

### Step 4: Verify
```bash
# Run specific test
bin/simple test path/to/spec.spl

# Check improvement
# Before: XXXXms
# After:  YYYYms
# Speedup: X.Xx
```

### Step 5: Document
- Update optimization guide with new patterns
- Note any new infrastructure created
- Track cumulative improvements

## Target Metrics

### Individual Test Goals
- **Basic tests:** < 1 second
- **Integration tests:** < 3 seconds
- **Performance tests:** < 5 seconds

### Suite-wide Goals
- **Top 10 tests:** < 25 seconds total (currently 85s)
- **Full suite:** < 2 minutes (currently 4+ minutes)
- **CI pipeline:** < 5 minutes end-to-end

## Infrastructure Checklist

Core infrastructure that should exist:

- ✅ **std.timing** - Timing and profiling
- ✅ **Value enum methods** - Type checking and accessors
- 🔲 **MockFileSystem** - In-memory file system
- 🔲 **TestDataBuilder** - Reusable test data construction
- 🔲 **CompilationCache** - Module caching across tests
- 🔲 **ParallelTestRunner** - Concurrent test execution

## Common Pitfalls

### ❌ Don't: Over-reduce test data
```simple
# Too small - might not catch edge cases
val elements = [for i in 0..5:  # Only 5 elements
    create_element(i)
]
```

### ✅ Do: Find the minimum that validates behavior
```simple
# Just right - enough to catch issues
val elements = [for i in 0..100:  # 100 elements
    create_element(i)
]
```

### ❌ Don't: Skip important edge cases
```simple
it "handles infinity":
    skip("division by zero not allowed")  # ← Lost coverage
```

### ✅ Do: Use runtime constants
```simple
it "handles infinity":
    val inf = runtime_infinity()  # ← Proper test
    expect inf.is_infinite()
```

### ❌ Don't: Split tests too granularly
```simple
# Too many tiny files
literal_converter_int_spec.spl        # 3 tests
literal_converter_float_spec.spl      # 3 tests
literal_converter_string_spec.spl     # 3 tests
# ... 20 more files
```

### ✅ Do: Group by logical category
```simple
# Balanced organization
literal_converter_basic_spec.spl       # 15 tests (primitives)
literal_converter_collections_spec.spl # 18 tests (arrays/dicts)
literal_converter_perf_spec.spl        #  5 tests (benchmarks)
```

## Next Steps

### Priority 1: Top 10 Slowest Tests
1. Apply same patterns to remaining 9 slowest tests
2. Expected: 85s → 20s (75% reduction)

### Priority 2: Infrastructure
1. Create MockFileSystem for I/O tests
2. Implement compilation caching
3. Build test data builders

### Priority 3: Automation
1. Add test profiling to CI
2. Flag regressions (tests getting slower)
3. Generate optimization suggestions automatically

---

**Status:** Active development
**Last Updated:** 2026-02-08
**Maintainer:** Test Infrastructure Team
