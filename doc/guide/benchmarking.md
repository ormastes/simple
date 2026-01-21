# Benchmarking Guide

**Status:** Implemented (Phase 1)
**Library:** `std.testing.benchmark`

## Overview

The benchmarking library provides statistical performance measurement for Simple functions. It includes warmup phases, outlier detection, and comparison capabilities.

## Quick Start

### Basic Benchmark

```simple
import std.testing.benchmark as bench

fn main():
    val stats = bench.benchmark_default("fibonacci", \:
        fibonacci(30)
    )

    print stats.summary()
```

**Output:**
```
Mean:     145.23 ms ± 2.31 ms
Median:   144.98 ms
Range:    [142.11 ms .. 151.45 ms]
Outliers: 0 low, 1 high
Samples:  10
```

### Compare Implementations

```simple
import std.testing.benchmark as bench

fn main():
    val data = generate_random_list(10000)

    val results = bench.compare_default({
        "quicksort": \: quicksort(data.clone()),
        "mergesort": \: mergesort(data.clone()),
        "heapsort": \: heapsort(data.clone())
    })

    for (name, stats) in results:
        print "{name}:"
        print stats.summary()
        print ""
```

## Configuration

### Default Configuration

```simple
val config = BenchmarkConfig.default()
# warmup_iterations: 3
# measurement_iterations: 100
# measurement_time_secs: 5.0
# sample_size: 10
# outlier_threshold: 3.0
# confidence_level: 0.95
```

### Quick Configuration

For fast iteration during development:

```simple
val config = BenchmarkConfig.quick()
# warmup_iterations: 1
# measurement_iterations: 50
# measurement_time_secs: 2.0
# sample_size: 3
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

## Understanding Results

### Statistics Explained

**Mean:** Average execution time across all samples
- Most commonly reported metric
- Affected by outliers

**Median:** Middle value when sorted
- More robust to outliers than mean
- Better for skewed distributions

**Standard Deviation:** Measure of variability
- Lower is better (more consistent)
- Used for outlier detection

**Outliers:** Measurements far from the mean
- Low outliers: Unusually fast (cache hits, etc.)
- High outliers: Unusually slow (GC, context switches, etc.)

### Interpreting Outliers

```
Outliers: 0 low, 1 high
```

- **0 outliers:** Very consistent performance ✅
- **Few outliers (1-2):** Normal variation 🆗
- **Many outliers (3+):** Investigate cause ⚠️

**Common causes:**
- Garbage collection pauses
- Operating system context switches
- Cache misses
- Thermal throttling

## Best Practices

### 1. Warmup is Important

Always use warmup iterations to:
- Prime CPU caches
- Trigger JIT compilation
- Stabilize system state

```simple
# Good: Default warmup
val stats = bench.benchmark_default("hot", \: hot_function())

# Bad: No warmup
val config = BenchmarkConfig.default().with(warmup_iterations: 0)
val stats = bench.benchmark("cold", \: cold_function(), config)
```

### 2. Minimize External Factors

```simple
# Good: Pure computation
fn pure_benchmark():
    var sum = 0
    for i in 0..1000:
        sum = sum + i
    sum

# Bad: I/O or randomness
fn flaky_benchmark():
    val file = File.read("/tmp/data.txt")  # I/O
    val rand = random.randint(0, 100)      # Non-deterministic
```

### 3. Use Comparison Mode

Don't guess which is faster, measure it:

```simple
val results = bench.compare_default({
    "approach_a": \: approach_a(data),
    "approach_b": \: approach_b(data)
})

# Find fastest
var fastest_name = ""
var fastest_time = f64.MAX

for (name, stats) in results:
    if stats.mean_ns < fastest_time:
        fastest_time = stats.mean_ns
        fastest_name = name

print "Fastest: {fastest_name}"
```

### 4. Clone Data for Fair Comparison

```simple
val data = generate_large_dataset()

# Good: Each implementation gets fresh data
val results = bench.compare_default({
    "in_place": \: sort_in_place(data.clone()),
    "copy": \: sort_copy(data.clone())
})

# Bad: Second implementation gets pre-sorted data
val results = bench.compare_default({
    "first": \: sort(data),   # Modifies data
    "second": \: sort(data)   # Already sorted!
})
```

## Integration with SSpec

### Basic Benchmark Test

```simple
import std.spec
import std.testing.benchmark as bench

describe "Performance tests":
    it "sorts 1000 items quickly":
        val data = generate_random_list(1000)

        val stats = bench.benchmark_default("sort", \:
            data.clone().sort()
        )

        print stats.summary()

        # Assert performance requirement
        expect stats.mean_ns < 10_000_000.0  # < 10ms
```

### Regression Detection

```simple
import std.spec
import std.testing.benchmark as bench

describe "Performance regressions":
    it "maintains O(n log n) complexity":
        # Benchmark with n=1000
        val small_data = generate_random_list(1000)
        val small_stats = bench.benchmark_default("n=1000", \:
            small_data.clone().sort()
        )

        # Benchmark with n=10000 (10x larger)
        val large_data = generate_random_list(10000)
        val large_stats = bench.benchmark_default("n=10000", \:
            large_data.clone().sort()
        )

        # Should be ~10 * log(10) = ~33x slower for O(n log n)
        # Allow 50x for safety margin
        val ratio = large_stats.mean_ns / small_stats.mean_ns
        expect ratio < 50.0, "Complexity worse than O(n log n)"
```

## Common Patterns

### Pattern 1: Micro-benchmarking

Testing individual operations:

```simple
describe "String operations benchmarks":
    it "concatenation":
        bench.benchmark_default("concat", \:
            "hello" + " " + "world"
        )

    it "formatting":
        bench.benchmark_default("format", \:
            "hello {name}".format(name: "world")
        )
```

### Pattern 2: Macro-benchmarking

Testing complete workflows:

```simple
fn simulate_web_request():
    val request = parse_http_request(sample_request)
    val response = handle_request(request)
    serialize_response(response)

val stats = bench.benchmark_default("web_request", simulate_web_request)
```

### Pattern 3: Before/After Optimization

```simple
fn old_implementation():
    # Naive algorithm
    for i in 0..n:
        for j in 0..n:
            compute(i, j)

fn new_implementation():
    # Optimized algorithm
    compute_all_at_once(n)

val results = bench.compare_default({
    "old": \: old_implementation(),
    "new": \: new_implementation()
})

val speedup = results["old"].mean_ns / results["new"].mean_ns
print "Speedup: {speedup:.2f}x"
```

## CI/CD Integration

### GitHub Actions Example

```yaml
name: Performance Benchmarks

on:
  push:
    branches: [main]
  pull_request:

jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Run benchmarks
        run: simple test benchmarks/

      - name: Check for regressions
        run: |
          # Compare with baseline
          simple bench --baseline baseline.json --compare current.json
```

### Tracking Performance Over Time

```simple
# Save benchmark results
val stats = bench.benchmark_default("critical_path", critical_function)
File.write("benchmarks/baseline.json", stats.to_json())

# Later, compare against baseline
val baseline = BenchmarkStats.from_json(File.read("benchmarks/baseline.json"))
val current = bench.benchmark_default("critical_path", critical_function)

if current.mean_ns > baseline.mean_ns * 1.1:
    print "⚠️  Performance regression detected!"
    print "Baseline: {BenchmarkStats.format_time(baseline.mean_ns)}"
    print "Current:  {BenchmarkStats.format_time(current.mean_ns)}"
    exit(1)
```

## Troubleshooting

### Problem: High Variance (Large Standard Deviation)

**Symptoms:**
```
Mean: 100.23 ms ± 45.67 ms  # 45% variance!
```

**Solutions:**
1. Increase sample size
2. Run on isolated machine (no background tasks)
3. Disable CPU frequency scaling
4. Check for GC pauses

### Problem: Many Outliers

**Symptoms:**
```
Outliers: 5 low, 8 high  # Too many!
```

**Solutions:**
1. Increase warmup iterations
2. Increase sample size
3. Check for external interference
4. Consider median instead of mean

### Problem: Inconsistent Results

**Symptoms:**
Running same benchmark twice gives different results.

**Solutions:**
1. Use longer measurement time
2. Increase sample size
3. Fix system state (disable turbo boost, etc.)
4. Use deterministic inputs

## Limitations

### What Benchmarking Can't Do

❌ **Replace profiling** - Doesn't show *where* time is spent
❌ **Predict production performance** - Synthetic workloads differ
❌ **Measure memory usage** - Only measures time
❌ **Catch all regressions** - Only tests what you measure

### When to Use Other Tools

- **Profiling:** Use when you need to find hot spots
- **Tracing:** Use when you need to understand execution flow
- **Load testing:** Use when you need to test under realistic load
- **Memory profiling:** Use when investigating memory usage

## Examples

See `simple/std_lib/test/unit/testing/benchmark_spec.spl` for more examples.

## API Reference

### Functions

**`benchmark(name, func, config)`**
- Benchmark a function with custom configuration
- Returns `BenchmarkStats`

**`benchmark_default(name, func)`**
- Benchmark with default configuration
- Returns `BenchmarkStats`

**`compare(benchmarks, config)`**
- Compare multiple implementations
- Returns `Map<text, BenchmarkStats>`

**`compare_default(benchmarks)`**
- Compare with default configuration
- Returns `Map<text, BenchmarkStats>`

### Types

**`BenchmarkConfig`**
- Configuration for benchmarks
- Presets: `default()`, `quick()`

**`BenchmarkStats`**
- Statistical results
- Methods: `summary()`, `format_time()`

## Further Reading

- [Criterion.rs Guide](https://bheisler.github.io/criterion.rs/book/) - Rust inspiration
- [hyperfine](https://github.com/sharkdp/hyperfine) - CLI benchmarking
- [The Rust Performance Book](https://nnethercote.github.io/perf-book/) - General advice
