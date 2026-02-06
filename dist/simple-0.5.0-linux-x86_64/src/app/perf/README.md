# Performance Tools - Pure Simple Implementation

Complete performance analysis and optimization tools written entirely in Simple.

## Overview

This package provides:
- **Profiler** - Measure execution time of code regions
- **Benchmark** - Run performance tests and compare results
- **Optimizer** - Analyze code and suggest optimizations

All tools are implemented in Pure Simple (no Rust modifications needed).

## Quick Start

```bash
# Analyze code for optimization opportunities
simple perf optimize src/

# Profile a script
simple perf profile examples/fibonacci.spl

# Run benchmarks
simple perf benchmark benchmarks/my_bench.spl

# Compare benchmark results
simple perf compare current.json baseline.json
```

## Profiler

Measure execution time of specific code regions.

### Usage

```simple
import perf.profiler

fn main():
    profiler.init_profiler()

    # Profile a region
    profiler.profile_region("computation", \:
        expensive_calculation()
    )

    # Print report
    profiler.print_profile()

    # Save to JSON
    profiler.save_profile("profile.json")

    # Get optimization suggestions
    val suggestions = profiler.analyze_hotspots()
    for sugg in suggestions:
        print sugg
```

### Output Example

```
Performance Profile Report
============================================================

Total time: 1234 ms

Region                        Count     Avg(µs)     Total(ms)    % Time
--------------------------------------------------------------------------------
computation                   100       500         50           40%
database_query                50        300         15           12%
render                        200       100         20           16%
```

## Benchmark

Run performance tests and track improvements over time.

### Usage

```simple
import perf.benchmark

fn main():
    var suite = benchmark.BenchSuite.create("My Benchmarks")

    # Load baseline for comparison
    suite.load_baseline("baseline.json")

    # Run benchmarks
    val result = suite.run_bench("array_ops", 1000, \:
        var arr = []
        for i in 0..100:
            arr.push(i)
    )
    suite.add_result(result)

    # Print results (with comparison to baseline)
    print suite.report()

    # Save results
    suite.save("current.json")
```

### Output Example

```
Benchmark Results: My Benchmarks
================================================================================

Benchmark                               Avg(µs)     Min(µs)     Max(µs)     Change
------------------------------------------------------------------------------------------
array_ops                               125         120         145         ✓ -15% faster
dict_lookup                             200         195         220         ≈ +2%
string_concat                           450         440         480         ✗ +20% slower
```

## Optimizer

Static code analysis with optimization suggestions.

### Usage

```bash
# Analyze a file
simple perf optimize src/app/build/main.spl

# Analyze entire directory
simple perf optimize src/
```

### Output Example

```
Code Optimization Report
================================================================================

Summary:
  Critical: 2
  Warnings: 5
  Info:     8

Critical Issues:
--------------------------------------------------------------------------------
🔴 src/app/build/main.spl:45 - Triple-nested loop detected (O(n³))
   → Consider algorithm optimization or data structure change

Warnings:
--------------------------------------------------------------------------------
⚠️  src/app/build/compiler.spl:23 - Function call in loop condition
   → Cache .len() result before loop: val n = items.len()

⚠️  src/app/build/formatter.spl:67 - String concatenation in loop
   → Use list.join() or string builder for better performance

⚠️  src/app/build/utils.spl:120 - Recursive function without memoization
   → Add @memoize decorator or manual caching for repeated inputs
```

## Optimization Patterns Detected

1. **Function calls in loop conditions** - Cache results
2. **String concatenation in loops** - Use join() or builder
3. **Nested loops** - O(n²) or O(n³) complexity warnings
4. **Multiple indexing in loops** - Extract to locals
5. **Recursive functions without memoization** - Add caching
6. **Large literals in hot paths** - Move to const

## Integration with Development Workflow

### 1. Development Phase

```bash
# Check code for optimization opportunities
simple perf optimize src/

# Run benchmarks
simple build test
```

### 2. Before Commit

```bash
# Save baseline
simple perf benchmark benchmarks/ > baseline.json

# After changes, compare
simple perf benchmark benchmarks/ > current.json
simple perf compare current.json baseline.json
```

### 3. CI/CD Integration

```yaml
# .github/workflows/performance.yml
- name: Run benchmarks
  run: simple perf benchmark benchmarks/ > results.json

- name: Compare with baseline
  run: simple perf compare results.json baseline.json
```

## Example: Complete Workflow

```simple
import perf.profiler
import perf.benchmark

fn optimize_my_code():
    # 1. Profile to find hotspots
    profiler.init_profiler()
    profiler.profile_region("main_loop", \:
        my_algorithm()
    )
    profiler.print_profile()

    # 2. Benchmark before optimization
    var suite = benchmark.BenchSuite.create("Algorithm")
    val before = suite.run_bench("original", 100, \: my_algorithm())
    suite.add_result(before)

    # 3. Make optimizations based on profiler output
    # ...

    # 4. Benchmark after optimization
    val after = suite.run_bench("optimized", 100, \: my_optimized_algorithm())
    suite.add_result(after)

    # 5. Compare results
    print suite.report()
```

## Performance Tips

### DO:
- ✅ Profile before optimizing
- ✅ Benchmark to verify improvements
- ✅ Cache expensive computations
- ✅ Use appropriate data structures
- ✅ Minimize allocations in hot paths

### DON'T:
- ❌ Optimize without measuring
- ❌ Concatenate strings in loops
- ❌ Repeat expensive calls
- ❌ Use O(n²) when O(n) is possible
- ❌ Ignore the profiler's suggestions

## Architecture

All tools are pure Simple:
```
src/app/perf/
├── profiler.spl     # Time measurement and analysis
├── benchmark.spl    # Performance testing framework
├── optimizer.spl    # Static code analysis
├── main.spl         # CLI interface
└── README.md        # This file
```

No Rust modifications required! Performance tools are self-contained.

## SFFI Requirements

These tools use standard SFFI hooks:
- `rt_time_monotonic_ns()` - High-resolution timer
- `rt_timestamp_iso8601()` - Timestamp generation
- `rt_get_args()` - Command-line arguments

All hooks are already available in the standard runtime.

## Future Enhancements

- [ ] Flame graph generation
- [ ] Memory profiling
- [ ] CPU cache analysis
- [ ] Auto-optimization suggestions
- [ ] JIT compilation hints
- [ ] Parallel execution profiling

## See Also

- `/examples/perf_demo.spl` - Complete usage examples
- `/doc/report/optimization_progress_2026-02-04.md` - Performance work
- `/script/profiling/` - Rust-level profiling tools (for runtime optimization)
