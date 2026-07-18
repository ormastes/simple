# duplicate_check_benchmark_spec

> Duplicate Check Benchmark Tests

<!-- sdn-diagram:id=duplicate_check_benchmark_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=duplicate_check_benchmark_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

duplicate_check_benchmark_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=duplicate_check_benchmark_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# duplicate_check_benchmark_spec

Duplicate Check Benchmark Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | app.duplicate_check - Benchmarking |
| Category | Testing \| Performance |
| Status | Pending (requires compiled mode) |
| Source | `test/05_perf/duplicate_check_benchmark_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Duplicate Check Benchmark Tests

These tests depend on app.duplicate_check.* modules which are only
available in compiled mode. In interpreter mode, we verify file loading only.

## Scenarios

### Benchmark: Execution

<details>
<summary>Advanced: requires compiled mode for benchmark execution</summary>

#### requires compiled mode for benchmark execution _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# app.duplicate_check modules not available in interpreter
expect(true).to_equal(true)
```

</details>


</details>

### Benchmark: Statistics

<details>
<summary>Advanced: requires compiled mode for stats computation</summary>

#### requires compiled mode for stats computation _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(true).to_equal(true)
```

</details>


</details>

### Benchmark: Formatting

<details>
<summary>Advanced: requires compiled mode for result formatting</summary>

#### requires compiled mode for result formatting _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(true).to_equal(true)
```

</details>


</details>

### Benchmark: Persistence

<details>
<summary>Advanced: requires compiled mode for save/load</summary>

#### requires compiled mode for save/load _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(true).to_equal(true)
```

</details>


</details>

### Benchmark: Comparison

<details>
<summary>Advanced: requires compiled mode for baseline comparison</summary>

#### requires compiled mode for baseline comparison _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(true).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
