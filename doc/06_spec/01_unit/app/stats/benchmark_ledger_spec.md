# Benchmark Ledger Specification

> Validates the benchmark ledger that measures C-baseline vs pure-Simple performance ratios across 5 hot-path categories: memcpy, string ops, file system, compress, and crypto.

<!-- sdn-diagram:id=benchmark_ledger_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=benchmark_ledger_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

benchmark_ledger_spec -> std
benchmark_ledger_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=benchmark_ledger_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Benchmark Ledger Specification

Validates the benchmark ledger that measures C-baseline vs pure-Simple performance ratios across 5 hot-path categories: memcpy, string ops, file system, compress, and crypto.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #hw-access-optimization-infra |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/pure_simple_lib_standalone_hw_plan.md |
| Source | `test/01_unit/app/stats/benchmark_ledger_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the benchmark ledger that measures C-baseline vs pure-Simple
performance ratios across 5 hot-path categories: memcpy, string ops,
file system, compress, and crypto.

## Behavior

- Each category has a C baseline obtained via libc extern fn calls
- Pure-Simple benchmark uses the std.benchmark harness
- Parity ratio = c_baseline_ns / pure_simple_ns
- Ledger output is a markdown table written to doc/10_metrics/

## Scenarios

### BenchmarkLedger

### HotPathCategory

#### AC-2: enum has all five required categories

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val memcpy_cat = HotPathCategory.Memcpy
val string_cat = HotPathCategory.StringOps
val fs_cat = HotPathCategory.FileSystem
val compress_cat = HotPathCategory.Compress
val crypto_cat = HotPathCategory.Crypto

# If we get here without error, all five variants exist
val memcpy_ok = memcpy_cat == HotPathCategory.Memcpy
expect(memcpy_ok).to_equal(true)
```

</details>

### run_category_benchmark

#### AC-2: returns BenchmarkStats for memcpy category

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = run_category_benchmark(HotPathCategory.Memcpy)

# BenchmarkStats should have a non-negative elapsed_ns
val elapsed = stats.elapsed_ns
expect(elapsed).to_be_greater_than(-1)
```

</details>

#### AC-2: returns BenchmarkStats for string ops category

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = run_category_benchmark(HotPathCategory.StringOps)

val elapsed = stats.elapsed_ns
expect(elapsed).to_be_greater_than(-1)
```

</details>

### c_baseline_for

#### AC-2: returns C baseline stats for memcpy

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_stats = c_baseline_for(HotPathCategory.Memcpy)

val elapsed = c_stats.elapsed_ns
expect(elapsed).to_be_greater_than(-1)
```

</details>

### compute_parity_ratio

#### AC-2: computes ratio as c_baseline / pure_simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pure_stats = run_category_benchmark(HotPathCategory.Memcpy)
val c_stats = c_baseline_for(HotPathCategory.Memcpy)
val ratio = compute_parity_ratio(pure_stats, c_stats)

# Ratio should be a positive number
expect(ratio).to_be_greater_than(0)
```

</details>

### generate_benchmark_ledger

#### AC-2: writes ledger report to specified path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = generate_benchmark_ledger("/tmp/test_ledger.md")

val is_ok = result.is_ok()
expect(is_ok).to_equal(true)
```

</details>

#### AC-2: ledger contains all five category rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = generate_benchmark_ledger("/tmp/test_ledger_rows.md")
val ledger_text = result.unwrap()

expect(ledger_text).to_contain("Memcpy")
expect(ledger_text).to_contain("StringOps")
expect(ledger_text).to_contain("FileSystem")
expect(ledger_text).to_contain("Compress")
expect(ledger_text).to_contain("Crypto")
```

</details>

#### AC-2: ledger contains ratio column

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = generate_benchmark_ledger("/tmp/test_ledger_ratio.md")
val ledger_text = result.unwrap()

expect(ledger_text).to_contain("ratio")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/pure_simple_lib_standalone_hw_plan.md](doc/03_plan/pure_simple_lib_standalone_hw_plan.md)


</details>
