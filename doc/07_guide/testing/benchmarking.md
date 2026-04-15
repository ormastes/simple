# Benchmarking Guide

Statistical performance measurement and test optimization for Simple.

---

## Table of Contents

1. [Quick Start](#quick-start)
2. [Configuration](#configuration)
3. [Understanding Results](#understanding-results)
4. [Comparison Mode](#comparison-mode)
5. [Integration with SSpec](#integration-with-sspec)
6. [Optimization Patterns](#optimization-patterns)
7. [CI/CD Integration](#cicd-integration)
8. [API Reference](#api-reference)
9. [Troubleshooting](#troubleshooting)

---

## Quick Start

**Library:** `std.testing.benchmark`

### Basic Benchmark

```simple
import std.testing.benchmark as bench

fn main():
    val stats = bench.benchmark_default("fibonacci", \:
        fibonacci(30)
    )
    print stats.summary()
```

Output:

```
Mean:     145.23 ms +/- 2.31 ms
Median:   144.98 ms
Range:    [142.11 ms .. 151.45 ms]
Outliers: 0 low, 1 high
Samples:  10
```

### Compare Implementations

```simple
val data = generate_random_list(10000)

val results = bench.compare_default({
    "quicksort": \: quicksort(data.clone()),
    "mergesort": \: mergesort(data.clone()),
    "heapsort": \: heapsort(data.clone())
})

for (name, stats) in results:
    print "{name}: {stats.summary()}"
```

---

## Configuration

### Presets

```simple
val config = BenchmarkConfig.default()
# warmup_iterations: 3, measurement_iterations: 100
# measurement_time_secs: 5.0, sample_size: 10
# outlier_threshold: 3.0, confidence_level: 0.95

val config = BenchmarkConfig.quick()
# warmup_iterations: 1, measurement_iterations: 50
# measurement_time_secs: 2.0, sample_size: 3
```

### Custom Configuration

```simple
val config = BenchmarkConfig(
    warmup_iterations: 5,
    measurement_iterations: 200,
    measurement_time_secs: 10.0,
    sample_size: 20,
    outlier_threshold: 2.5,
    confidence_level: 0.99
)

val stats = bench.benchmark("custom", \: my_function(), config)
```

---

## Understanding Results

### Statistics

| Metric | Description | Notes |
|--------|-------------|-------|
| **Mean** | Average execution time | Affected by outliers |
| **Median** | Middle value when sorted | More robust than mean |
| **Standard Deviation** | Measure of variability | Lower is better |
| **Outliers (low)** | Unusually fast runs | Cache hits, etc. |
| **Outliers (high)** | Unusually slow runs | GC, context switches |

### Interpreting Outliers

- **0 outliers** -- Very consistent performance
- **1-2 outliers** -- Normal variation
- **3+ outliers** -- Investigate: GC pauses, OS context switches, cache misses, thermal throttling

---

## Comparison Mode

Always clone data for fair comparison:

```simple
val data = generate_large_dataset()

# Good: Each implementation gets fresh data
val results = bench.compare_default({
    "in_place": \: sort_in_place(data.clone()),
    "copy": \: sort_copy(data.clone())
})

# Bad: Second gets pre-sorted data
val results = bench.compare_default({
    "first": \: sort(data),
    "second": \: sort(data)  # Already sorted!
})
```

Find the fastest:

```simple
var fastest_name = ""
var fastest_time = f64.MAX
for (name, stats) in results:
    if stats.mean_ns < fastest_time:
        fastest_time = stats.mean_ns
        fastest_name = name
print "Fastest: {fastest_name}"
```

---

## Integration with SSpec

### Performance Test

```simple
import std.spec
import std.testing.benchmark as bench

describe "Performance tests":
    it "sorts 1000 items quickly":
        val data = generate_random_list(1000)
        val stats = bench.benchmark_default("sort", \:
            data.clone().sort()
        )
        expect stats.mean_ns < 10_000_000.0  # < 10ms
```

### Regression Detection

```simple
describe "Performance regressions":
    it "maintains O(n log n) complexity":
        val small = bench.benchmark_default("n=1000", \:
            generate_random_list(1000).sort()
        )
        val large = bench.benchmark_default("n=10000", \:
            generate_random_list(10000).sort()
        )
        # Should be ~33x slower for O(n log n), allow 50x margin
        val ratio = large.mean_ns / small.mean_ns
        expect ratio < 50.0
```

---

## Optimization Patterns

### Pattern 1: Reduce Test Data Size

The most effective optimization. 10x data reduction typically yields ~10x speedup.

```simple
# Before (slow -- 10k elements)
slow_it "handles large arrays":
    val elements = [for i in 0..10000: create_element(i)]

# After (fast -- 1k elements, still validates behavior)
slow_it "handles large arrays":
    val elements = [for i in 0..1000: create_element(i)]
```

### Pattern 2: Split Large Test Files

When a test file has 40+ tests and takes 5+ seconds:

```
# Before: single file
literal_converter_spec.spl           # 48 tests, 16s

# After: split by category
literal_converter_basic_spec.spl      # 15 tests, 2s
literal_converter_collections_spec.spl # 18 tests, 3s
literal_converter_perf_spec.spl       #  5 tests, 4s
```

### Pattern 3: Mock External Resources

```simple
# Before (slow -- actual file I/O)
it "reads config":
    file_write("test.conf", "key=value")
    val config = load_config("test.conf")

# After (fast -- in-memory)
it "reads config":
    val mock_fs = MockFileSystem()
    mock_fs.add("test.conf", "key=value")
    val config = load_config_from("test.conf", mock_fs)
```

### Pattern 4: Use Test Data Builders

```simple
fn build_test_array(size: i64) -> Value:
    val elements = [for i in 0..size: Value.Int(i)]
    Value.Array(elements)

it "handles arrays":
    val arr = build_test_array(100)
    expect arr.is_array()
```

### Pattern 5: Before/After Optimization Comparison

```simple
val results = bench.compare_default({
    "old": \: old_implementation(),
    "new": \: new_implementation()
})

val speedup = results["old"].mean_ns / results["new"].mean_ns
print "Speedup: {speedup:.2f}x"
```

### Optimization Workflow

1. **Measure**: `bin/simple test --only-slow` to find slowest tests
2. **Analyze**: Check for large loops, oversized data, missing imports, external I/O
3. **Fix**: Apply quick wins first (reduce data 10x, fix APIs, add mocks)
4. **Verify**: Run specific test and compare timing
5. **Document**: Note patterns and infrastructure created

### Target Metrics

| Category | Target |
|----------|--------|
| Basic tests | < 1 second |
| Integration tests | < 3 seconds |
| Performance tests | < 5 seconds |
| Full suite | < 2 minutes |
| CI pipeline | < 5 minutes |

---

## CI/CD Integration

### GitHub Actions

```yaml
name: Performance Benchmarks
on:
  push:
    branches: [main]

jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run benchmarks
        run: simple test benchmarks/
      - name: Check for regressions
        run: simple bench --baseline baseline.json --compare current.json
```

### Tracking Performance Over Time

```simple
val stats = bench.benchmark_default("critical_path", critical_function)
File.write("benchmarks/baseline.json", stats.to_json())

# Later, compare:
val baseline = BenchmarkStats.from_json(File.read("benchmarks/baseline.json"))
val current = bench.benchmark_default("critical_path", critical_function)

if current.mean_ns > baseline.mean_ns * 1.1:
    print "Performance regression detected!"
    exit(1)
```

---

## API Reference

### Functions

| Function | Description | Returns |
|----------|-------------|---------|
| `benchmark(name, func, config)` | Benchmark with custom config | `BenchmarkStats` |
| `benchmark_default(name, func)` | Benchmark with defaults | `BenchmarkStats` |
| `compare(benchmarks, config)` | Compare multiple implementations | `Map<text, BenchmarkStats>` |
| `compare_default(benchmarks)` | Compare with defaults | `Map<text, BenchmarkStats>` |

### Types

**`BenchmarkConfig`** -- Configuration with presets `default()` and `quick()`.

**`BenchmarkStats`** -- Statistical results with `summary()` and `format_time()` methods. Fields: `mean_ns`, `median_ns`, `std_dev_ns`, `min_ns`, `max_ns`, `low_outliers`, `high_outliers`.

---

## Troubleshooting

### High variance (large standard deviation)

1. Increase sample size and warmup iterations
2. Run on idle machine (no background tasks)
3. Disable CPU frequency scaling
4. Check for GC pauses

### Many outliers

1. Increase warmup iterations (prime caches, trigger JIT)
2. Increase sample size
3. Consider using median instead of mean

### Inconsistent results between runs

1. Use longer measurement time
2. Fix system state (disable turbo boost)
3. Use deterministic inputs
4. Avoid I/O or randomness in benchmarks

### Limitations

- Does not show WHERE time is spent (use profiling for that)
- Synthetic workloads may not predict production performance
- Only measures time, not memory usage
- Only tests what you measure
