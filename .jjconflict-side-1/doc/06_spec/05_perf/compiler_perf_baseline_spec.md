# Compiler Performance Baseline

> Compiler Performance Baseline Tests

<!-- sdn-diagram:id=compiler_perf_baseline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_perf_baseline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_perf_baseline_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_perf_baseline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Performance Baseline

Compiler Performance Baseline Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Performance Audit Round 1 |
| Category | Performance \| Testing |
| Status | Implemented |
| Source | `test/05_perf/compiler_perf_baseline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Compiler Performance Baseline Tests

Measures wall-clock microseconds for critical compiler hot-path operations.
Uses rt_time_now_unix_micros() for timing.
Note: interpreter mode only verifies file loading (it block bodies don't execute).

## Scenarios

### Compiler Performance Baseline

<details>
<summary>Advanced: struct field access completes within threshold</summary>

#### struct field access completes within threshold _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bench_struct_field_access())
```

</details>


</details>

<details>
<summary>Advanced: array push completes within threshold</summary>

#### array push completes within threshold _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bench_array_push())
```

</details>


</details>

<details>
<summary>Advanced: array slice completes within threshold</summary>

#### array slice completes within threshold _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bench_array_slice())
```

</details>


</details>

<details>
<summary>Advanced: dict lookup completes within threshold</summary>

#### dict lookup completes within threshold _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bench_dict_lookup())
```

</details>


</details>

<details>
<summary>Advanced: string substring completes within threshold</summary>

#### string substring completes within threshold _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bench_string_substring())
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
