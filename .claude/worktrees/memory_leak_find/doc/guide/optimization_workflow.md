# Optimization Workflow Guide

Complete guide to optimizing Simple code using Pure Simple performance tools.

## Quick Start

```bash
# 1. Analyze code for issues
simple perf optimize examples/opt_before.spl

# 2. Run baseline benchmark
simple examples/opt_before.spl

# 3. Apply optimizations
simple examples/opt_after.spl

# 4. Compare results
simple perf compare benchmark_after.json benchmark_before.json
```

## Step-by-Step Workflow

### Step 1: Identify Performance Issues

Use the optimizer to scan for common performance problems:

```bash
simple perf optimize src/
```

**Output:**
```
Code Optimization Report
================================================================================

Critical Issues:
--------------------------------------------------------------------------------
🔴 examples/opt_before.spl:15 - Triple-nested loop detected (O(n³))
   → Consider algorithm optimization or data structure change

Warnings:
--------------------------------------------------------------------------------
⚠️  examples/opt_before.spl:8 - String concatenation in loop
   → Use list.join() or string builder for better performance

⚠️  examples/opt_before.spl:13 - Function call in loop condition
   → Cache .len() result before loop: val n = items.len()

⚠️  examples/opt_before.spl:25 - Recursive function without memoization
   → Add @memoize decorator or manual caching for repeated inputs
```

### Step 2: Measure Current Performance

Run benchmarks to establish baseline:

```simple
import perf.benchmark

var suite = benchmark.BenchSuite.create("Baseline")

val result = suite.run_bench("slow_function", 1000, \:
    slow_function()
)
suite.add_result(result)

print suite.report()
suite.save("baseline.json")
```

**Output:**
```
Benchmark Results: Baseline
================================================================================
Benchmark                               Avg(µs)     Min(µs)     Max(µs)
------------------------------------------------------------------------------------------
build_report                            850         820         920
process_data                            450         430         480
find_duplicates                         12000       11500       13000
fibonacci                               8500        8200        8900
sum_values                              2500        2400        2700
```

### Step 3: Apply Optimizations

Fix issues identified by the optimizer:

#### Fix 1: String Concatenation in Loop

**Before (O(n²)):**
```simple
fn build_report(items: List<text>) -> text:
    var report = ""
    for item in items:
        report = report + item + "\n"  # ❌ Creates new string each time
    report
```

**After (O(n)):**
```simple
fn build_report(items: List<text>) -> text:
    var parts = []
    for item in items:
        parts.push(item)  # ✅ Append to list
    parts.join("\n")  # ✅ Single join
```

**Expected improvement:** 10-50x faster for large lists

#### Fix 2: Function Calls in Loop

**Before:**
```simple
for i in 0..data.len():  # ❌ Calls .len() every iteration
    if data[i] > data.len() / 2:  # ❌ Calls .len() again!
        result.push(data[i])
```

**After:**
```simple
val n = data.len()  # ✅ Cache result
val threshold = n / 2  # ✅ Calculate once
for i in 0..n:
    if data[i] > threshold:
        result.push(data[i])
```

**Expected improvement:** 2-3x faster

#### Fix 3: Nested Loops → Better Algorithm

**Before (O(n²)):**
```simple
fn find_duplicates(items: List<i64>) -> List<i64>:
    var duplicates = []
    for i in 0..items.len():
        for j in (i + 1)..items.len():  # ❌ Nested loop
            if items[i] == items[j]:
                duplicates.push(items[i])
    duplicates
```

**After (O(n)):**
```simple
fn find_duplicates(items: List<i64>) -> List<i64>:
    var seen = {}
    var duplicates = {}

    for item in items:  # ✅ Single pass
        if seen.contains_key(item):
            duplicates[item] = true
        else:
            seen[item] = true

    duplicates.keys()
```

**Expected improvement:** 100-1000x faster for large lists

#### Fix 4: Add Memoization

**Before (O(2^n)):**
```simple
fn fibonacci(n: i64) -> i64:
    if n <= 1: return n
    fibonacci(n - 1) + fibonacci(n - 2)  # ❌ Recalculates values
```

**After (O(n)):**
```simple
var CACHE: Dict<i64, i64> = {}

fn fibonacci(n: i64) -> i64:
    if n <= 1: return n

    if CACHE.contains_key(n):  # ✅ Check cache
        return CACHE[n]

    val result = fibonacci(n - 1) + fibonacci(n - 2)
    CACHE[n] = result  # ✅ Cache result
    result
```

**Expected improvement:** 1000-10000x faster for n > 20

#### Fix 5: Hoist Loop-Invariant Code

**Before:**
```simple
for item in data:
    for _ in 0..100:  # ❌ Nested loop
        if lookup.contains_key(item):  # ❌ Double lookup
            total = total + lookup[item]
```

**After:**
```simple
for item in data:
    if val Some(value) = lookup.get(item):  # ✅ Single lookup
        total = total + (value * 100)  # ✅ Hoist multiplication
```

**Expected improvement:** 5-10x faster

### Step 4: Measure Improvement

Run benchmarks again and compare:

```simple
var suite = benchmark.BenchSuite.create("Optimized")
suite.load_baseline("baseline.json")

# Run same benchmarks...

print suite.report()
```

**Output:**
```
Benchmark Results: Optimized
================================================================================
Benchmark                               Avg(µs)     Min(µs)     Max(µs)     Change
------------------------------------------------------------------------------------------
build_report                            25          22          30          ✓ -97% faster
process_data                            150         145         160         ✓ -67% faster
find_duplicates                         120         115         130         ✓ -99% faster
fibonacci                               8           7           10          ✓ -99.9% faster
sum_values                              250         240         270         ✓ -90% faster
```

### Step 5: Profile for Further Optimization

Use the profiler to find remaining hotspots:

```simple
import perf.profiler

fn main():
    profiler.init_profiler()

    profiler.profile_region("data_processing", \:
        process_all_data()
    )

    profiler.profile_region("report_generation", \:
        generate_report()
    )

    profiler.print_profile()
    val suggestions = profiler.analyze_hotspots()
```

**Output:**
```
Performance Profile Report
============================================================

Region                        Count     Avg(µs)     Total(ms)    % Time
--------------------------------------------------------------------------------
data_processing               1         450         450          75%
report_generation             1         150         150          25%

Optimization Suggestions:
  ⚠️  'data_processing' is slow (avg 450µs) - consider optimization
```

## Common Optimization Patterns

### 1. Cache Expensive Computations

```simple
# Before
for item in items:
    process(expensive_computation())

# After
val cached_value = expensive_computation()
for item in items:
    process(cached_value)
```

### 2. Use Appropriate Data Structures

```simple
# Before: Linear search O(n)
fn contains(list: List<i64>, value: i64) -> bool:
    for item in list:
        if item == value:
            return true
    false

# After: Hash lookup O(1)
val set = {}
for item in list:
    set[item] = true

fn contains(set: Dict<i64, bool>, value: i64) -> bool:
    set.contains_key(value)
```

### 3. Avoid Repeated String Building

```simple
# Before: O(n²)
var html = ""
for tag in tags:
    html = html + "<" + tag + ">"

# After: O(n)
var parts = []
for tag in tags:
    parts.push("<" + tag + ">")
html = parts.join("")
```

### 4. Minimize Allocations

```simple
# Before: Creates new list every time
fn filter_positive(data: List<i64>) -> List<i64>:
    [for x in data if x > 0: x]

# After: Reuse result list
fn filter_positive(data: List<i64>) -> List<i64>:
    var result = []
    for x in data:
        if x > 0:
            result.push(x)
    result
```

### 5. Early Exit

```simple
# Before: Checks all items
fn has_large_value(data: List<i64>) -> bool:
    var found = false
    for x in data:
        if x > 1000:
            found = true
    found

# After: Exits immediately
fn has_large_value(data: List<i64>) -> bool:
    for x in data:
        if x > 1000:
            return true
    false
```

## Performance Checklist

Before committing code, verify:

- [ ] No string concatenation in loops
- [ ] Function calls cached outside loops
- [ ] Appropriate data structures (Set/Dict for lookups)
- [ ] Memoization for recursive functions
- [ ] No nested loops over large data
- [ ] Early exit conditions
- [ ] Minimal allocations in hot paths

## Benchmarking Best Practices

1. **Run warmup iterations** - First runs are slower
2. **Use sufficient iterations** - At least 100 for reliable stats
3. **Test with realistic data** - Not just tiny examples
4. **Measure multiple times** - Check for variance
5. **Compare with baseline** - Track improvements over time

## Tools Reference

```bash
# Analyze code
simple perf optimize <file|dir>

# Profile execution
simple perf profile <file>

# Run benchmarks
simple perf benchmark <file>

# Compare results
simple perf compare current.json baseline.json
```

## Example Projects

- `/examples/opt_before.spl` - Code with performance issues
- `/examples/opt_after.spl` - Optimized version
- `/examples/perf_demo.spl` - Complete profiling demo

## Next Steps

1. Run optimizer on your code: `simple perf optimize src/`
2. Fix critical issues first (🔴)
3. Then warnings (⚠️ )
4. Benchmark before and after
5. Iterate until performance goals met

Happy optimizing! 🚀
