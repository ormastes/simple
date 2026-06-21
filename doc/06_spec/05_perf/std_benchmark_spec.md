# std_benchmark_spec

> Std Benchmark Library Tests

<!-- sdn-diagram:id=std_benchmark_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=std_benchmark_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

std_benchmark_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=std_benchmark_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std_benchmark_spec

Std Benchmark Library Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Testing Infrastructure - Benchmarking |
| Category | Testing \| Performance |
| Status | Active |
| Source | `test/05_perf/std_benchmark_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Std Benchmark Library Tests

Tests for the `std.testing.benchmark` library.
Note: Many benchmark operations chain methods which are not supported
in interpreter mode. Tests use intermediate variables to work around this.

## Scenarios

### Benchmarking Library

<details>
<summary>Advanced: default config has correct warmup</summary>

#### default config has correct warmup _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = benchmark_config_default()
expect(config.warmup_iterations).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: default config has correct measurement iterations</summary>

#### default config has correct measurement iterations _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = benchmark_config_default()
expect(config.measurement_iterations).to_equal(100)
```

</details>


</details>

<details>
<summary>Advanced: default config has correct sample size</summary>

#### default config has correct sample size _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = benchmark_config_default()
expect(config.sample_size).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: quick config has warmup of 1</summary>

#### quick config has warmup of 1 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = benchmark_config_quick()
expect(config.warmup_iterations).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: quick config has sample size of 3</summary>

#### quick config has sample size of 3 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = benchmark_config_quick()
expect(config.sample_size).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: custom config has correct sample size</summary>

#### custom config has correct sample size _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = BenchmarkConfig(
    warmup_iterations: 1,
    measurement_iterations: 50,
    sample_size: 5,
    outlier_threshold: 1.5
)
expect(config.sample_size).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats nanoseconds</summary>

#### format_time formats nanoseconds _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_time(500.0)
val has_ns = _text_contains(result, "ns")
expect(has_ns).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats microseconds</summary>

#### format_time formats microseconds _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_time(1500.0)
val has_us = _text_contains(result, "us")
expect(has_us).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats milliseconds</summary>

#### format_time formats milliseconds _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_time(1500000.0)
val has_ms = _text_contains(result, "ms")
expect(has_ms).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: format_time formats seconds</summary>

#### format_time formats seconds _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = format_time(1500000000.0)
val has_s = _text_contains(result, "s")
expect(has_s).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
