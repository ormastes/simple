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
| `pure_dl_perf.spl` | Deep learning performance comparison (Pure Simple vs PyTorch FFI) | Run directly: `bin/simple test/perf/pure_dl_perf.spl` |
| `run_duplicate_check.spl` | Duplicate detection performance benchmark | `bin/simple test/perf/run_duplicate_check.spl [path] [options]` |
| `native_layout_performance_spec.spl` | Native code layout performance tests | Run with test runner |
| `profile_scripts/profile_report_contract_test.shs` | Common contract test for profile scripts that generate Markdown under `doc/09_report` | Called by profile scripts; can run directly with kind, script path, and report path |
| `profile_scripts/profile_report_contract_negative_test.shs` | Negative mutation coverage for the cross-language report contract | Mutates temporary report copies and expects failures for slow Go fanout, slow Simple multicore-green fanout/stress, missing runtime-pool/counter evidence, bad OS-thread labels, cooperative-green M:N or missing-current-thread claims, SMF-baseline/pherallel profile drift, and forbidden numbered API names |
| `profile_scripts/profile_help_contract_test.shs` | Cross-language profile help contract | Verifies `--help` prints usage and exits before expensive workload compilation starts |
| `profile_scripts/profile_binary_autoselect_test.shs` | Cross-language profile Simple-binary auto-selection regression | Runs a reduced profile and verifies stale wrappers are skipped |
| `profile_scripts/profile_docker_isolation_contract_test.shs` | Cross-language profile Docker isolation contract | Stubs Docker and verifies the profile re-execs with network disabled, memory/CPU limits, UID/GID mapping, workspace mount, and env handoff |
| `profile_scripts/concurrency_api_contract_test.shs` | Public concurrency API misuse and naming contract | Verifies approved OS-thread, task-pool, cooperative-green, and multicore-green imports while rejecting wrong surfaces, direct `rt_pool_*` access, shared mutable green captures, numeric-suffix concurrency aliases, and native resolver coverage for `rt_pool_*` counter symbols |
| `stress/multicore_green_large_profile_gate_spec.spl` | Simple SSpec companion gate for the checked-in large cross-language report | Parses `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md` and checks Go fanout, Simple multicore-green runtime-pool evidence, work-stealing queue evidence, and C pthread baselines |

## Quick Start

### Running Standard Benchmarks

```bash
# Run compiler/runtime benchmarks
bin/simple test/perf/compiler_runtime.spl

# Run DL performance benchmarks
bin/simple test/perf/pure_dl_perf.spl

# Run duplicate detection benchmarks
bin/simple test/perf/run_duplicate_check.spl src/ --iterations 5
```

### Using the Benchmark Framework

```simple
use std.text.{NL}

# Import from compiler_runtime.spl
# (Note: This is a local module, adjust imports as needed)

val config = BenchmarkConfig.quick()
var runner = BenchmarkRunner.create(config)

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
val my_benchmark = Benchmark.create("custom_test", \\:
    # Your code to benchmark
    var sum = 0
    for i in 0..10000:
        sum = sum + i
    pass
).with_description("Sum 0 to 9999")
 .with_category("math")

# Run it
var runner = BenchmarkRunner.default_runner()
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

### Profile Script Reports
- **Cross-language profile:** `scripts/check/check-cross-language-perf.shs`
- **GUI profile:** `tools/gui_perf_bench/run_all_benchmarks.shs`
- **Common report contract:** `test/05_perf/profile_scripts/profile_report_contract_test.shs` (no args checks the canonical checked-in cross-language report, `doc/09_report/README.md`, and `doc/03_plan/agent_tasks/multicore_green.md`, printing `report_index_checked=doc/09_report/README.md` and `agent_task_plan_checked=doc/03_plan/agent_tasks/multicore_green.md`; profile wrappers pass kind, script path, and report path explicitly)
- **Negative report mutations:** `test/05_perf/profile_scripts/profile_report_contract_negative_test.shs` keeps Go-vs-C, Simple-vs-C, OS-thread, cooperative-green current-OS-thread wording, runtime-pool/counter evidence, SMF-baseline separation, and forbidden-numbered-name failures release-visible
- **Profile help guard:** `test/05_perf/profile_scripts/profile_help_contract_test.shs` checks that `scripts/check/check-cross-language-perf.shs --help` prints usage without starting compilation
- **Large profile SSpec gate:** `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl` checks the current checked-in report's large Go fanout, Simple multicore-green fanout/stress, `pool_used=`, `parallelism=`, `counter_delta=`, and `queue_model=work_stealing` evidence
- **Profile binary auto-selection:** `test/05_perf/profile_scripts/profile_binary_autoselect_test.shs` checks that auto mode probes candidates and skips stale release wrappers
- **Profile Docker isolation:** `test/05_perf/profile_scripts/profile_docker_isolation_contract_test.shs` checks the crash-containment re-exec command without requiring a Docker daemon
- **Concurrency API contract:** `test/05_perf/profile_scripts/concurrency_api_contract_test.shs` checks meaningful public API names, rejects numeric-suffix concurrency aliases, and stays paired with `cargo test -p simple-compiler elf_utils::tests::resolves_runtime_pool_symbols` so native `rt_pool_*` counter symbols cannot disappear while profile rows still claim counter-qualified M:N evidence
- **Report location:** `doc/09_report/*.md`

## Benchmark Configuration

### Quick (for CI)
```simple
val config = BenchmarkConfig.quick()
# - 1 warmup iteration
# - 3 measurement iterations
# - 10ms minimum duration
# - 10s maximum duration
```

### Default (standard)
```simple
val config = BenchmarkConfig.default_config()
# - 3 warmup iterations
# - 10 measurement iterations
# - 100ms minimum duration
# - 60s maximum duration
```

### Thorough (release validation)
```simple
val config = BenchmarkConfig.thorough()
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
bin/simple test/perf/run_duplicate_check.spl src/ --save baseline.txt

# Make changes...

# Compare with baseline
bin/simple test/perf/run_duplicate_check.spl src/ --compare baseline.txt
```

## Related Tools

- **Performance Analysis:** `src/app/perf/` - CLI tools for profiling, optimization analysis
- **Benchmarking Library:** `src/lib/src/testing/benchmark.spl` - Stdlib benchmark utilities
- **Example Code:** `src/lib/examples/testing/benchmark_example.spl`

## See Also

- [Testing Guide](../../doc/guide/benchmarking.md) - Detailed benchmarking methodology
- [Performance Reports](../../doc/report/) - Performance analysis documents
- [Optimization Plans](../../doc/research/) - Performance optimization research

---

**Note:** Benchmarks in this directory are **executables**, not test specs. They measure performance, not correctness. For correctness testing, see `test/unit/`, `test/integration/`, and `test/system/`.
