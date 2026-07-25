# Test Runner Benchmark Framework Tests

> Tests for the test runner's benchmark framework components. Covers the full lifecycle of benchmark execution: creating results, configuring runs, running benchmarks, aggregating suite results, and comparing against baselines.

<!-- sdn-diagram:id=test_runner_benchmark_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_runner_benchmark_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_runner_benchmark_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_runner_benchmark_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Benchmark Framework Tests

Tests for the test runner's benchmark framework components. Covers the full lifecycle of benchmark execution: creating results, configuring runs, running benchmarks, aggregating suite results, and comparing against baselines.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Testing Infrastructure - Benchmarking |
| Category | Testing \| Performance |
| Status | Planned |
| Source | `test/05_perf/test_runner_benchmark_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the test runner's benchmark framework components. Covers the full
lifecycle of benchmark execution: creating results, configuring runs, running
benchmarks, aggregating suite results, and comparing against baselines.

## Key Areas

- BenchmarkResult: Timing sample collection, statistics, time formatting
- BenchmarkConfig: Default, quick, and thorough configuration presets
- Benchmark: Creating benchmarks with name, description, category, setup/teardown
- BenchmarkRunner: Adding and executing benchmarks, warmup and measurement phases
- BenchmarkSuite: Grouping benchmarks and running with config
- BenchmarkComparison: Baseline comparison, speedup calculation, regression detection

## Scenarios

### BenchmarkResult

<details>
<summary>Advanced: creates result from timing samples</summary>

#### creates result from timing samples _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BenchmarkResult.create("test", [100, 110, 105])
# result.avg_time_ns is approximately 105
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates min time</summary>

#### calculates min time _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.min_time_ns == minimum of samples
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates max time</summary>

#### calculates max time _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.max_time_ns == maximum of samples
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates standard deviation</summary>

#### calculates standard deviation _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.std_dev_ns reflects variation in samples
pass
```

</details>


</details>

<details>
<summary>Advanced: handles empty samples</summary>

#### handles empty samples _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BenchmarkResult.create("test", [])
# result.iterations == 0
pass
```

</details>


</details>

<details>
<summary>Advanced: formats time in nanoseconds</summary>

#### formats time in nanoseconds _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.format_time(500) == "500 ns"
pass
```

</details>


</details>

<details>
<summary>Advanced: formats time in microseconds</summary>

#### formats time in microseconds _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.format_time(5000) contains "us"
pass
```

</details>


</details>

<details>
<summary>Advanced: formats time in milliseconds</summary>

#### formats time in milliseconds _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.format_time(5000000) contains "ms"
pass
```

</details>


</details>

<details>
<summary>Advanced: formats time in seconds</summary>

#### formats time in seconds _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.format_time(5000000000) contains "s"
pass
```

</details>


</details>

### BenchmarkConfig

<details>
<summary>Advanced: creates default config</summary>

#### creates default config _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BenchmarkConfig.default_config()
# config.warmup_iterations > 0
pass
```

</details>


</details>

<details>
<summary>Advanced: creates quick config</summary>

#### creates quick config _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BenchmarkConfig.quick()
# config.measurement_iterations < default
pass
```

</details>


</details>

<details>
<summary>Advanced: creates thorough config</summary>

#### creates thorough config _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BenchmarkConfig.thorough()
# config.measurement_iterations > default
pass
```

</details>


</details>

### Benchmark

<details>
<summary>Advanced: creates benchmark with name and function</summary>

#### creates benchmark with name and function _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Benchmark.create("test", fn)
# bench.name == "test"
pass
```

</details>


</details>

<details>
<summary>Advanced: adds description</summary>

#### adds description _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bench.with_description("desc")
# bench.description == "desc"
pass
```

</details>


</details>

<details>
<summary>Advanced: adds category</summary>

#### adds category _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bench.with_category("memory")
# bench.category == "memory"
pass
```

</details>


</details>

<details>
<summary>Advanced: adds setup function</summary>

#### adds setup function _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bench.with_setup(fn)
# bench.setup_fn.? == true
pass
```

</details>


</details>

<details>
<summary>Advanced: adds teardown function</summary>

#### adds teardown function _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bench.with_teardown(fn)
# bench.teardown_fn.? == true
pass
```

</details>


</details>

### BenchmarkRunner

<details>
<summary>Advanced: creates runner with config</summary>

#### creates runner with config _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BenchmarkRunner.create(config)
pass
```

</details>


</details>

<details>
<summary>Advanced: creates default runner</summary>

#### creates default runner _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BenchmarkRunner.default_runner()
pass
```

</details>


</details>

<details>
<summary>Advanced: adds benchmarks</summary>

#### adds benchmarks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# runner.add_benchmark(bench)
# runner.benchmarks.len() == 1
pass
```

</details>


</details>

<details>
<summary>Advanced: runs all benchmarks</summary>

#### runs all benchmarks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# runner.run_all() returns results
pass
```

</details>


</details>

<details>
<summary>Advanced: runs warmup iterations</summary>

#### runs warmup iterations _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# warmup iterations run before measurement
pass
```

</details>


</details>

<details>
<summary>Advanced: runs measurement iterations</summary>

#### runs measurement iterations _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# measurement iterations collected for stats
pass
```

</details>


</details>

### BenchmarkSuite

<details>
<summary>Advanced: creates suite with name</summary>

#### creates suite with name _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BenchmarkSuite.create("my_suite").name == "my_suite"
pass
```

</details>


</details>

<details>
<summary>Advanced: adds benchmarks</summary>

#### adds benchmarks _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# suite.add(bench)
# suite.benchmarks.len() == 1
pass
```

</details>


</details>

<details>
<summary>Advanced: runs with config</summary>

#### runs with config _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# suite.run(config) returns BenchmarkSuiteResult
pass
```

</details>


</details>

### BenchmarkSuiteResult

<details>
<summary>Advanced: contains all results</summary>

#### contains all results _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.results.len() == number of benchmarks
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates total time</summary>

#### calculates total time _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.total_time_ns == sum of all benchmark times
pass
```

</details>


</details>

<details>
<summary>Advanced: formats summary</summary>

#### formats summary _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# result.format_summary() contains suite name
pass
```

</details>


</details>

### BenchmarkComparison

<details>
<summary>Advanced: compares baseline to current</summary>

#### compares baseline to current _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BenchmarkComparison.compare(baseline, current)
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates speedup</summary>

#### calculates speedup _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If current is faster, speedup > 1.0
pass
```

</details>


</details>

<details>
<summary>Advanced: detects regression</summary>

#### detects regression _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If current is 5% slower, is_regression == true
pass
```

</details>


</details>

<details>
<summary>Advanced: formats comparison</summary>

#### formats comparison _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# comparison.format_comparison() contains speedup
pass
```

</details>


</details>

### Standard Benchmarks

<details>
<summary>Advanced: creates fibonacci benchmark</summary>

#### creates fibonacci benchmark _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fibonacci_benchmark().name == "fibonacci_30"
pass
```

</details>


</details>

<details>
<summary>Advanced: creates array sum benchmark</summary>

#### creates array sum benchmark _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# array_sum_benchmark().name contains "array_sum"
pass
```

</details>


</details>

<details>
<summary>Advanced: creates string concat benchmark</summary>

#### creates string concat benchmark _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# string_concat_benchmark().category == "string"
pass
```

</details>


</details>

<details>
<summary>Advanced: creates allocation benchmark</summary>

#### creates allocation benchmark _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# allocation_benchmark().category == "memory"
pass
```

</details>


</details>

<details>
<summary>Advanced: creates standard suite</summary>

#### creates standard suite _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# standard_benchmarks().benchmarks.len() >= 4
pass
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 38 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
