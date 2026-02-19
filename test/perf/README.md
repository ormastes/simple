# Performance Benchmarks

This directory contains performance benchmarks for the Simple Language compiler and runtime.

## Overview

Benchmarks are used to:
- Measure compiler and runtime performance
- Track performance regressions across versions
- Compare different optimization strategies
- Validate performance improvements

## Benchmark Files

| File | Description | Usage |
|------|-------------|-------|
| `compiler_runtime.spl` | Core benchmark framework and standard benchmarks (fibonacci, array operations, string concat, memory allocation) | Import and use BenchmarkRunner API |
| `pure_dl_perf.spl` | Deep learning performance comparison (Pure Simple vs PyTorch FFI) | Run directly: `bin/simple test/benchmarks/pure_dl_perf.spl` |
| `run_duplicate_check.spl` | Duplicate detection performance benchmark | `bin/simple test/benchmarks/run_duplicate_check.spl [path] [options]` |
| `native_layout_performance_spec.spl` | Native code layout performance tests | Run with test runner |

## Quick Start

### Running Standard Benchmarks

```bash
# Run compiler/runtime benchmarks
bin/simple test/benchmarks/compiler_runtime.spl

# Run DL performance benchmarks
bin/simple test/benchmarks/pure_dl_perf.spl

# Run duplicate detection benchmarks
bin/simple test/benchmarks/run_duplicate_check.spl src/ --iterations 5
```

### Using the Benchmark Framework

```simple
use std.text.{NL}

# Import from compiler_runtime.spl
# (Note: This is a local module, adjust imports as needed)

val config = BenchmarkConfig__quick()
var runner = BenchmarkRunner__create(config)

# Add standard benchmarks
runner.add_benchmark(fibonacci_benchmark())
runner.add_benchmark(array_sum_benchmark())

# Run all benchmarks
val results = runner.run_all()

# Print results
for result in results:
    print result.format_result()
```

### Custom Benchmarks

```simple
# Create a custom benchmark
val my_benchmark = Benchmark__create("custom_test", \\:
    # Your code to benchmark
    var sum = 0
    for i in 0..10000:
        sum = sum + i
    pass
).with_description("Sum 0 to 9999")
 .with_category("math")

# Run it
var runner = BenchmarkRunner__default_runner()
runner.add_benchmark(my_benchmark)
val results = runner.run_all()
```

## Benchmark Categories

### Compiler/Runtime
- **Compilation:** Measure compile time for different code patterns
- **Runtime:** Measure execution time for common operations
- **Memory:** Measure allocation and garbage collection overhead
- **Throughput:** Operations per second

### Deep Learning
- **Tensor Creation:** zeros, ones, randn (10×10, 100×100, 1000×1000)
- **Element-wise Operations:** add, mul, div (various sizes)
- **Matrix Multiplication:** matmul (critical path, 10×10 to 1000×1000)
- **Activation Functions:** relu, sigmoid, tanh
- **Memory Management:** Leak testing with 1000+ operations

### Code Analysis
- **Duplicate Detection:** File scanning, token matching, block identification
- **Static Analysis:** Code pattern recognition, optimization suggestions

## Benchmark Configuration

### Quick (for CI)
```simple
val config = BenchmarkConfig__quick()
# - 1 warmup iteration
# - 3 measurement iterations
# - 10ms minimum duration
# - 10s maximum duration
```

### Default (standard)
```simple
val config = BenchmarkConfig__default_config()
# - 3 warmup iterations
# - 10 measurement iterations
# - 100ms minimum duration
# - 60s maximum duration
```

### Thorough (release validation)
```simple
val config = BenchmarkConfig__thorough()
# - 10 warmup iterations
# - 100 measurement iterations
# - 1s minimum duration
# - 5 minutes maximum duration
```

## Output Format

Benchmark results include:
- **Iterations:** Number of measurement runs
- **Min/Max/Avg:** Time statistics in nanoseconds
- **Std Dev:** Standard deviation (variability indicator)
- **Throughput:** Operations per second (optional)

Example output:
```
Benchmark: fibonacci_30
  Iterations: 10
  Min:  45.2 ms
  Max:  52.1 ms
  Avg:  48.3 ms
  Std:  2.1 ms
```

## Performance Tips

### For Accurate Results
1. **Close background applications** before running benchmarks
2. **Use thorough config** for release validation
3. **Run multiple times** and compare averages
4. **Disable CPU frequency scaling** for consistent results
5. **Warm up** before measurement (already handled by framework)

### Interpreting Results
- **Speedup < 2x:** Marginal improvement
- **Speedup 2-10x:** Significant improvement, worth optimizing
- **Speedup > 10x:** Critical optimization, essential for production

### Comparing Results
```bash
# Save baseline
bin/simple test/benchmarks/run_duplicate_check.spl src/ --save baseline.txt

# Make changes...

# Compare with baseline
bin/simple test/benchmarks/run_duplicate_check.spl src/ --compare baseline.txt
```

## Related Tools

- **Performance Analysis:** `src/app/perf/` - CLI tools for profiling, optimization analysis
- **Benchmarking Library:** `src/std/src/testing/benchmark.spl` - Stdlib benchmark utilities
- **Example Code:** `src/std/examples/testing/benchmark_example.spl`

## See Also

- [Testing Guide](../../doc/guide/benchmarking.md) - Detailed benchmarking methodology
- [Performance Reports](../../doc/report/) - Performance analysis documents
- [Optimization Plans](../../doc/research/) - Performance optimization research

---

**Note:** Benchmarks in this directory are **executables**, not test specs. They measure performance, not correctness. For correctness testing, see `test/unit/`, `test/integration/`, and `test/system/`.
