# Test Runner Benchmark Specification

> Tests covering BenchmarkResult, BenchmarkConfig, Benchmark, BenchmarkRunner, BenchmarkSuite, BenchmarkSuiteResult, BenchmarkComparison, Standard Benchmarks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Benchmark Specification

## Scenarios

### BenchmarkResult

<details>
<summary>Advanced: creates result from timing samples</summary>

#### creates result from timing samples _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates result from timing samples


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates result from timing samples")
# BenchmarkResult.create("test", [100, 110, 105])
# result.avg_time_ns is approximately 105
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates min time</summary>

#### calculates min time _(slow)_

- calculates min time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("calculates min time")
# result.min_time_ns == minimum of samples
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates max time</summary>

#### calculates max time _(slow)_

- calculates max time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("calculates max time")
# result.max_time_ns == maximum of samples
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates standard deviation</summary>

#### calculates standard deviation _(slow)_

- calculates standard deviation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("calculates standard deviation")
# result.std_dev_ns reflects variation in samples
pass
```

</details>


</details>

<details>
<summary>Advanced: handles empty samples</summary>

#### handles empty samples _(slow)_

- handles empty samples


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("handles empty samples")
# BenchmarkResult.create("test", [])
# result.iterations == 0
pass
```

</details>


</details>

<details>
<summary>Advanced: formats time in nanoseconds</summary>

#### formats time in nanoseconds _(slow)_

- formats time in nanoseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("formats time in nanoseconds")
# result.format_time(500) == "500 ns"
pass
```

</details>


</details>

<details>
<summary>Advanced: formats time in microseconds</summary>

#### formats time in microseconds _(slow)_

- formats time in microseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("formats time in microseconds")
# result.format_time(5000) contains "us"
pass
```

</details>


</details>

<details>
<summary>Advanced: formats time in milliseconds</summary>

#### formats time in milliseconds _(slow)_

- formats time in milliseconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("formats time in milliseconds")
# result.format_time(5000000) contains "ms"
pass
```

</details>


</details>

<details>
<summary>Advanced: formats time in seconds</summary>

#### formats time in seconds _(slow)_

- formats time in seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("formats time in seconds")
# result.format_time(5000000000) contains "s"
pass
```

</details>


</details>

### BenchmarkConfig

<details>
<summary>Advanced: creates default config</summary>

#### creates default config _(slow)_

- creates default config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates default config")
# BenchmarkConfig.default_config()
# config.warmup_iterations > 0
pass
```

</details>


</details>

<details>
<summary>Advanced: creates quick config</summary>

#### creates quick config _(slow)_

- creates quick config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates quick config")
# BenchmarkConfig.quick()
# config.measurement_iterations < default
pass
```

</details>


</details>

<details>
<summary>Advanced: creates thorough config</summary>

#### creates thorough config _(slow)_

- creates thorough config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates thorough config")
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

- creates benchmark with name and function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates benchmark with name and function")
# Benchmark.create("test", fn)
# bench.name == "test"
pass
```

</details>


</details>

<details>
<summary>Advanced: adds description</summary>

#### adds description _(slow)_

- adds description


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("adds description")
# bench.with_description("desc")
# bench.description == "desc"
pass
```

</details>


</details>

<details>
<summary>Advanced: adds category</summary>

#### adds category _(slow)_

- adds category


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("adds category")
# bench.with_category("memory")
# bench.category == "memory"
pass
```

</details>


</details>

<details>
<summary>Advanced: adds setup function</summary>

#### adds setup function _(slow)_

- adds setup function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("adds setup function")
# bench.with_setup(fn)
# bench.setup_fn != nil
pass
```

</details>


</details>

<details>
<summary>Advanced: adds teardown function</summary>

#### adds teardown function _(slow)_

- adds teardown function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("adds teardown function")
# bench.with_teardown(fn)
# bench.teardown_fn != nil
pass
```

</details>


</details>

### BenchmarkRunner

<details>
<summary>Advanced: creates runner with config</summary>

#### creates runner with config _(slow)_

- creates runner with config


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates runner with config")
# BenchmarkRunner.create(config)
pass
```

</details>


</details>

<details>
<summary>Advanced: creates default runner</summary>

#### creates default runner _(slow)_

- creates default runner


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates default runner")
# BenchmarkRunner.default_runner()
pass
```

</details>


</details>

<details>
<summary>Advanced: adds benchmarks</summary>

#### adds benchmarks _(slow)_

- adds benchmarks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("adds benchmarks")
# runner.add_benchmark(bench)
# runner.benchmarks.len() == 1
pass
```

</details>


</details>

<details>
<summary>Advanced: runs all benchmarks</summary>

#### runs all benchmarks _(slow)_

- runs all benchmarks


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("runs all benchmarks")
# runner.run_all() returns results
pass
```

</details>


</details>

<details>
<summary>Advanced: runs warmup iterations</summary>

#### runs warmup iterations _(slow)_

- runs warmup iterations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("runs warmup iterations")
# warmup iterations run before measurement
pass
```

</details>


</details>

<details>
<summary>Advanced: runs measurement iterations</summary>

#### runs measurement iterations _(slow)_

- runs measurement iterations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("runs measurement iterations")
# measurement iterations collected for stats
pass
```

</details>


</details>

### BenchmarkSuite

<details>
<summary>Advanced: creates suite with name</summary>

#### creates suite with name _(slow)_

- creates suite with name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates suite with name")
# BenchmarkSuite.create("my_suite").name == "my_suite"
pass
```

</details>


</details>

<details>
<summary>Advanced: adds benchmarks</summary>

#### adds benchmarks _(slow)_

- adds benchmarks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("adds benchmarks")
# suite.add(bench)
# suite.benchmarks.len() == 1
pass
```

</details>


</details>

<details>
<summary>Advanced: runs with config</summary>

#### runs with config _(slow)_

- runs with config


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("runs with config")
# suite.run(config) returns BenchmarkSuiteResult
pass
```

</details>


</details>

### BenchmarkSuiteResult

<details>
<summary>Advanced: contains all results</summary>

#### contains all results _(slow)_

- contains all results


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("contains all results")
# result.results.len() == number of benchmarks
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates total time</summary>

#### calculates total time _(slow)_

- calculates total time


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("calculates total time")
# result.total_time_ns == sum of all benchmark times
pass
```

</details>


</details>

<details>
<summary>Advanced: formats summary</summary>

#### formats summary _(slow)_

- formats summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("formats summary")
# result.format_summary() contains suite name
pass
```

</details>


</details>

### BenchmarkComparison

<details>
<summary>Advanced: compares baseline to current</summary>

#### compares baseline to current _(slow)_

- compares baseline to current


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("compares baseline to current")
# BenchmarkComparison.compare(baseline, current)
pass
```

</details>


</details>

<details>
<summary>Advanced: calculates speedup</summary>

#### calculates speedup _(slow)_

- calculates speedup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("calculates speedup")
# If current is faster, speedup > 1.0
pass
```

</details>


</details>

<details>
<summary>Advanced: detects regression</summary>

#### detects regression _(slow)_

- detects regression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("detects regression")
# If current is 5% slower, is_regression == true
pass
```

</details>


</details>

<details>
<summary>Advanced: formats comparison</summary>

#### formats comparison _(slow)_

- formats comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("formats comparison")
# comparison.format_comparison() contains speedup
pass
```

</details>


</details>

### Standard Benchmarks

<details>
<summary>Advanced: creates fibonacci benchmark</summary>

#### creates fibonacci benchmark _(slow)_

- creates fibonacci benchmark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates fibonacci benchmark")
# fibonacci_benchmark().name == "fibonacci_30"
pass
```

</details>


</details>

<details>
<summary>Advanced: creates array sum benchmark</summary>

#### creates array sum benchmark _(slow)_

- creates array sum benchmark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates array sum benchmark")
# array_sum_benchmark().name contains "array_sum"
pass
```

</details>


</details>

<details>
<summary>Advanced: creates string concat benchmark</summary>

#### creates string concat benchmark _(slow)_

- creates string concat benchmark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates string concat benchmark")
# string_concat_benchmark().category == "string"
pass
```

</details>


</details>

<details>
<summary>Advanced: creates allocation benchmark</summary>

#### creates allocation benchmark _(slow)_

- creates allocation benchmark


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates allocation benchmark")
# allocation_benchmark().category == "memory"
pass
```

</details>


</details>

<details>
<summary>Advanced: creates standard suite</summary>

#### creates standard suite _(slow)_

- creates standard suite


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("creates standard suite")
# standard_benchmarks().benchmarks.len() >= 4
pass
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/test_runner_benchmark_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BenchmarkResult, BenchmarkConfig, Benchmark, BenchmarkRunner, BenchmarkSuite, BenchmarkSuiteResult, BenchmarkComparison, Standard Benchmarks.
- BenchmarkResult
- BenchmarkConfig
- Benchmark
- BenchmarkRunner
- BenchmarkSuite
- BenchmarkSuiteResult
- BenchmarkComparison
- Standard Benchmarks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 38 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c69a7b6826733020bcbff9289546569f942c7c3a2cd87019ad6e9a07883b4908`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c69a7b6826733020bcbff9289546569f942c7c3a2cd87019ad6e9a07883b4908`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c69a7b6826733020bcbff9289546569f942c7c3a2cd87019ad6e9a07883b4908`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/05_perf/test_runner_benchmark_spec.spl
mirror: doc/06_spec/05_perf/test_runner_benchmark_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/05_perf/test_runner_benchmark_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/test_runner_benchmark_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/test_runner_benchmark_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/05_perf/test_runner_benchmark_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates result from timing samples' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/test_runner_benchmark_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calculates min time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/test_runner_benchmark_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calculates max time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
