# Testing Infrastructure Compatibility Report

**Date:** 2026-01-21
**Status:** ⚠️ Implementation uses features not yet available in Simple
**Files Affected:** `benchmark.spl`, `deployment.spl`

## Executive Summary

The Phase 1 & 2 implementation (benchmarking and smoke testing) uses several features that are **not yet available** in Simple's standard library. This report identifies all incompatibilities and proposes solutions.

**Critical Findings:**
- ❌ `std.time` module doesn't exist
- ❌ `Map<K, V>` type doesn't exist (used in 7 locations)
- ❌ `try/catch` exception handling not available
- ✅ `Result<T, E>` type exists
- ✅ `List<T>` type exists
- ✅ `math.sqrt()` exists

## Detailed Compatibility Analysis

### 1. Time Module (BLOCKING)

**Issue:** Implementation uses `import std.time` which doesn't exist.

**Used Features:**
```simple
// In benchmark.spl
import std.time                           // ❌ Module doesn't exist
val start = time.now_nanos()             // ❌ Function doesn't exist
val duration_ms = time.now_ms() - start  // ❌ Function doesn't exist

// In deployment.spl
import std.time                           // ❌ Module doesn't exist
val start = time.now_ms()                 // ❌ Function doesn't exist
time.sleep(config.retry_delay_secs)      // ❌ Function doesn't exist
val elapsed = time.now() - start          // ❌ Function doesn't exist
```

**Available Alternatives:**
```simple
// Found in src/lib/std/src/host/async_nogc_mut/datetime.spl
extern fn rt_time_now_unix_micros() -> i32  // ✅ Microsecond precision (not nanoseconds!)

// Found in src/lib/std/src/concurrency/threads.spl
extern fn rt_thread_sleep(millis: i64)       // ✅ Sleep function exists!
fn sleep(millis: i64):                       // ✅ High-level wrapper
    rt_thread_sleep(millis)
```

**Problem:** Benchmarking needs **nanosecond** precision, but Simple only has **microsecond** precision.

**Impact:**
- Benchmarking: Cannot accurately measure fast operations (<1ms)
- Smoke testing: Cannot implement sleep/timeout properly

---

### 2. Map Type (BLOCKING)

**Issue:** Implementation uses `Map<K, V>` which doesn't exist in Simple's stdlib.

**Used Locations:**
```simple
// In benchmark.spl (line 204, 206, 227, 229)
pub fn compare(
    benchmarks: Map<text, fn()>,    // ❌ Map type doesn't exist
    config: BenchmarkConfig
) -> Map<text, BenchmarkStats>:     // ❌ Map type doesn't exist
    var results = {}                 // ❌ Map literal doesn't exist
    for (name, func) in benchmarks:  // ❌ Can't iterate Map
        results[name] = ...          // ❌ Can't index Map
    results

pub fn compare_default(benchmarks: Map<text, fn()>) -> Map<text, BenchmarkStats>
```

**Available Alternatives:**
```simple
// Found in src/lib/std/src/core_nogc/small_map.spl
struct SmallMap<K, V, const N: i32>  // ✅ EXISTS but limited capacity

// Map<K,V> is referenced but not defined anywhere!
// SmallMap internally uses Map<K,V> which also doesn't exist!
```

**Problem:** No general-purpose dictionary/map type in Simple stdlib.

**Impact:**
- Benchmarking: Cannot implement comparison mode
- Cannot store name → statistics mappings

---

### 3. Exception Handling (BLOCKING)

**Issue:** Implementation uses `try/catch` which is not available in Simple.

**Used Location:**
```simple
// In deployment.spl (line 279-289)
fn run_with_timeout(
    func: fn() -> bool,
    timeout_secs: f64
) -> Result<bool, text>:
    try:                              // ❌ try/catch doesn't exist
        val start = time.now()
        val result = func()
        val elapsed = time.now() - start

        if elapsed > timeout_secs:
            Err("Timeout")
        else:
            Ok(result)
    catch e:                          // ❌ try/catch doesn't exist
        Err(e.to_string())
```

**Available Alternatives:**
```simple
// Result<T, E> exists at src/lib/std/src/compiler_core/result.spl ✅
enum Result<T, E>:
    Ok(T)
    Err(E)

// But no try/catch syntax - must use match expressions
match risky_operation():
    case Ok(v): // handle success
    case Err(e): // handle error
```

**Problem:** Simple doesn't have exception handling, only Result types.

**Impact:**
- Cannot catch runtime errors from test functions
- Must assume test functions never panic
- Timeout detection won't work

---

## Feature Availability Summary

| Feature | Status | Location | Notes |
|---------|--------|----------|-------|
| **Result<T, E>** | ✅ Available | `src/lib/std/src/compiler_core/result.spl` | Full implementation |
| **Option<T>** | ✅ Available | `src/lib/std/src/compiler_core/option.spl` | Full implementation |
| **List<T>** | ✅ Available | `src/lib/std/src/compiler_core/list.spl` | Full implementation |
| **math.sqrt()** | ✅ Available | `src/lib/std/src/compiler_core/math.spl` | Full math library |
| **Map<K, V>** | ❌ Missing | N/A | Referenced but not defined |
| **std.time** | ❌ Missing | N/A | Module doesn't exist |
| **time.now_nanos()** | ❌ Missing | N/A | Only microseconds available |
| **time.now_ms()** | ❌ Missing | N/A | Only microseconds available |
| **time.sleep()** | ⚠️ Partial | `src/lib/std/src/concurrency/threads.spl` | `sleep(millis: i64)` exists but in threads module |
| **rt_thread_sleep()** | ✅ Available | `src/lib/std/src/concurrency/threads.spl` | FFI sleep function (milliseconds) |
| **try/catch** | ❌ Missing | N/A | Not part of language |
| **Microsecond timing** | ⚠️ Partial | `src/lib/std/src/host/async_nogc_mut/datetime.spl` | `rt_time_now_unix_micros()` |

---

## Proposed Solutions

### Solution A: Minimal Adaptation (RECOMMENDED)

Adapt implementation to use only existing Simple features.

**Changes Required:**

#### 1. Replace std.time with FFI calls
```simple
# benchmark.spl
# Remove: import std.time
# Add:
extern fn rt_time_now_unix_micros() -> i32

fn now_micros() -> i32:
    rt_time_now_unix_micros()

fn now_nanos() -> i64:
    # Approximate: microseconds * 1000
    rt_time_now_unix_micros() as i64 * 1000

# Replace time.now_nanos() with now_nanos()
# Replace time.now_ms() with now_micros() / 1000
```

**Pros:**
- Works with existing Simple features
- No new dependencies
- Can implement today

**Cons:**
- Lower precision (microseconds, not nanoseconds)
- Fast benchmarks (<1μs) won't be accurate

---

#### 2. Replace Map<K,V> with List<(K,V)>
```simple
# benchmark.spl
# Replace:
pub fn compare(
    benchmarks: Map<text, fn()>,
    config: BenchmarkConfig
) -> Map<text, BenchmarkStats>

# With:
pub fn compare(
    benchmarks: List<(text, fn())>,
    config: BenchmarkConfig
) -> List<(text, BenchmarkStats)>

# Replace:
var results = {}
for (name, func) in benchmarks:
    results[name] = benchmark(name, func, config)

# With:
var results = []
for (name, func) in benchmarks:
    results.append((name, benchmark(name, func, config)))
```

**Pros:**
- Works with existing List type
- No new types needed
- Can iterate and access values

**Cons:**
- O(n) lookup instead of O(1)
- Less ergonomic than Map
- Users must pass List<(K,V)> instead of Map

---

#### 3. Remove try/catch, assume functions don't panic
```simple
# deployment.spl
fn run_with_timeout(
    func: fn() -> bool,
    timeout_secs: f64
) -> Result<bool, text>:
    # Remove try/catch
    # Assume func() never panics
    val start = now_micros()
    val result = func()
    val elapsed = now_micros() - start

    if (elapsed as f64 / 1_000_000.0) > timeout_secs:
        Err("Timeout")
    else:
        Ok(result)

    # NOTE: Cannot catch panics, function will crash on error
```

**Pros:**
- Works with existing features
- Simple implementation

**Cons:**
- Cannot catch test errors
- Test panics will crash entire suite
- Timeout detection is approximate (happens AFTER test completes)

---

### Solution B: Implement Missing Features (FUTURE)

Create the missing stdlib modules.

**Required Work:**

#### 1. Create std.time module
```simple
# simple/std_lib/src/time.spl
extern fn rt_time_now_unix_micros() -> i32
extern fn rt_sleep_micros(micros: i32)

pub fn now_micros() -> i64:
    rt_time_now_unix_micros() as i64

pub fn now_nanos() -> i64:
    rt_time_now_unix_micros() as i64 * 1000

pub fn now_ms() -> i64:
    rt_time_now_unix_micros() as i64 / 1000

pub fn now() -> f64:
    rt_time_now_unix_micros() as f64 / 1_000_000.0

pub fn sleep(seconds: f64):
    rt_sleep_micros((seconds * 1_000_000.0) as i32)

export now_micros
export now_nanos
export now_ms
export now
export sleep
```

**Requires:**
- Implementing `rt_sleep_micros()` in Rust runtime
- Adding to stdlib exports

---

#### 2. Create Map<K,V> type
```simple
# simple/std_lib/src/compiler_core/map.spl
# Basic hash map implementation
struct Map<K, V>:
    buckets: List<List<(K, V)>>
    len: i32

    static fn new() -> Map<K, V>
    fn insert(key: K, value: V) -> Option<V>
    fn get(key: K) -> Option<V>
    fn remove(key: K) -> Option<V>
    fn contains_key(key: K) -> bool
    fn len() -> i32
    fn is_empty() -> bool
    # ... etc
```

**Requires:**
- Hash function for keys
- Bucket management
- Collision handling
- ~300-500 LOC implementation

---

#### 3. Add exception handling (DEFERRED)
This requires language-level changes, not just stdlib work.

**Alternative:** Document that test functions must return `Result<bool, text>` instead of throwing.

---

## Implementation Options

### Option 1: Minimal Working Version (1-2 hours)

**Scope:**
- ✅ Benchmarking with microsecond precision (adapt to Solution A.1)
- ✅ Smoke testing without sleep/timeout (remove those features)
- ❌ Comparison mode (skip until Map exists)
- ❌ Proper error handling (tests must not panic)

**Files to modify:**
1. `benchmark.spl` - Replace time module with FFI calls
2. `benchmark.spl` - Remove comparison functions (compare, compare_default)
3. `deployment.spl` - Replace time module with FFI calls
4. `deployment.spl` - Remove try/catch, document limitations
5. `benchmark_example.spl` - Remove comparison example
6. `smoke_test_example.spl` - Remove retry/sleep examples

**Result:** Minimal working libraries with known limitations.

---

### Option 2: Create std.time module (3-4 hours)

**Scope:**
- ✅ Implement std.time module (Solution B.1)
- ✅ Benchmarking with time module
- ✅ Smoke testing with sleep (but not timeout)
- ❌ Comparison mode (still need Map)
- ❌ Proper error handling

**Additional work:**
1. Create `simple/std_lib/src/time.spl`
2. Implement `rt_sleep_micros()` in Rust runtime
3. Add exports to `__init__.spl`
4. Update implementation to use std.time
5. Test time module

**Result:** Professional time module, still no Map or exceptions.

---

### Option 3: Full Implementation (1-2 weeks)

**Scope:**
- ✅ Implement std.time module
- ✅ Implement Map<K, V> type
- ✅ Benchmarking fully working
- ✅ Smoke testing with retries and sleep
- ⚠️ Exception handling (document as limitation)

**Additional work:**
1. Create std.time module (3-4 hours)
2. Create Map<K, V> implementation (~1-2 days)
3. Write Map tests (~1 day)
4. Update all implementations
5. Update all examples
6. Update all documentation

**Result:** Production-ready testing libraries (except exception handling).

---

## Recommended Path Forward

### Immediate Action (This Session)

**Choose one:**

1. **Document as blocked** - Mark Phase 1 & 2 as blocked pending stdlib features
   - Update implementation summary
   - List missing dependencies
   - Wait for stdlib development

2. **Create minimal working version** (Option 1)
   - 1-2 hours of work
   - Working benchmarks (microsecond precision)
   - Working smoke tests (no timeout)
   - Clear documentation of limitations

3. **Implement std.time module** (Option 2)
   - 3-4 hours of work
   - Professional time API
   - Still need Map for comparison mode

### Long-term Strategy

**Phase 3a: stdlib foundation (Q1 2026)**
- Implement std.time module
- Implement Map<K, V> type
- These are generally useful, not just for testing

**Phase 3b: Complete testing infrastructure (Q2 2026)**
- Unblock benchmarking and smoke testing
- Implement mock library (still blocked on trait objects)
- Full feature set

---

## Recommendations

**For Simple Language Development:**
1. **Priority: Implement Map<K, V>** - fundamental collection type missing
2. **Priority: Create std.time module** - essential for any time-based operations
3. **Consider: Exception handling** - Result<T,E> is good but try/catch would help

**For Testing Infrastructure:**
1. **Short-term:** Document as blocked, create issue for dependencies
2. **Medium-term:** Implement std.time and Map (1 week work)
3. **Long-term:** Complete all features once dependencies ready

---

## Conclusion

The testing infrastructure implementation is **well-designed** but uses features that **don't exist yet** in Simple's standard library. Three critical dependencies are missing:

1. ❌ **std.time** - No time module (only FFI calls)
2. ❌ **Map<K, V>** - No dictionary type
3. ❌ **try/catch** - No exception handling

**Recommendation:** Either:
- **Option A:** Create minimal std.time and Map modules (~1 week)
- **Option B:** Document as blocked, wait for stdlib development
- **Option C:** Adapt to use only existing features (degraded functionality)

The user should decide which path to take based on priorities.

---

**Next Steps:**
1. User decides: Implement dependencies vs. adapt implementation vs. defer
2. If implement: Start with std.time module (highest impact, easiest)
3. If adapt: Use Solution A (minimal changes, works today)
4. If defer: Mark as blocked, create tracking issues
