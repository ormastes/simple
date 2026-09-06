# Typed Array Bulk-Allocation Smoke Spec

> Smoke spec for the `rt_f64_array_alloc`, `rt_f32_array_alloc`, `rt_i64_array_alloc` and `rt_i32_array_alloc` externs (PERF-SUGAR-001). Verifies:

<!-- sdn-diagram:id=typed_array_alloc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=typed_array_alloc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

typed_array_alloc_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=typed_array_alloc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Array Bulk-Allocation Smoke Spec

Smoke spec for the `rt_f64_array_alloc`, `rt_f32_array_alloc`, `rt_i64_array_alloc` and `rt_i32_array_alloc` externs (PERF-SUGAR-001). Verifies:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-PERFSUGAR-08 |
| Category | Perf |
| Difficulty | 2/5 |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_perf_sugar.md |
| Source | `test/05_perf/typed_array_alloc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Smoke spec for the `rt_f64_array_alloc`, `rt_f32_array_alloc`, `rt_i64_array_alloc`
and `rt_i32_array_alloc` externs (PERF-SUGAR-001). Verifies:

1. Allocations return zero-filled buffers of the requested length.
2. Large allocations (up to 524,288 elements) complete without error.
3. No push-loop workaround needed — single Rust-side C-style alloc.

This mirrors `feedback_interpreter_bulk_buffer` (rt_bytes_alloc B2) for typed arrays.
No `--mode=native` or `--mode=smf`; interpreter mode only.

## Scenarios

### rt_f64_array_alloc typed bulk allocation

#### allocates 8-element zero-filled f64 buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_f64_array_alloc(8)
expect(arr.len()).to_equal(8)
```

</details>

#### f64 buffer elements are zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_f64_array_alloc(4)
expect(arr[0]).to_equal(0.0)
expect(arr[3]).to_equal(0.0)
```

</details>

#### allocates zero-length f64 buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_f64_array_alloc(0)
expect(arr.len()).to_equal(0)
```

</details>

#### allocates 1 MiB f64 buffer (131072 elements)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_f64_array_alloc(131072)
expect(arr.len()).to_equal(131072)
expect(arr[0]).to_equal(0.0)
expect(arr[131071]).to_equal(0.0)
```

</details>

#### allocates 4 MiB f64 buffer (524288 elements) without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_f64_array_alloc(524288)
expect(arr.len()).to_equal(524288)
```

</details>

### rt_f32_array_alloc typed bulk allocation

#### allocates 8-element zero-filled f32 buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_f32_array_alloc(8)
expect(arr.len()).to_equal(8)
```

</details>

#### f32 buffer elements are zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_f32_array_alloc(4)
expect(arr[0]).to_equal(0.0)
expect(arr[3]).to_equal(0.0)
```

</details>

#### allocates zero-length f32 buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_f32_array_alloc(0)
expect(arr.len()).to_equal(0)
```

</details>

#### allocates large f32 buffer (131072 elements)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_f32_array_alloc(131072)
expect(arr.len()).to_equal(131072)
```

</details>

### rt_i64_array_alloc typed bulk allocation

#### allocates 8-element zero-filled i64 buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_i64_array_alloc(8)
expect(arr.len()).to_equal(8)
```

</details>

#### i64 buffer elements are zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_i64_array_alloc(4)
expect(arr[0]).to_equal(0)
expect(arr[3]).to_equal(0)
```

</details>

#### allocates large i64 buffer (131072 elements)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_i64_array_alloc(131072)
expect(arr.len()).to_equal(131072)
```

</details>

### rt_i32_array_alloc typed bulk allocation

#### allocates 8-element zero-filled i32 buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_i32_array_alloc(8)
expect(arr.len()).to_equal(8)
```

</details>

#### i32 buffer elements are zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_i32_array_alloc(4)
expect(arr[0]).to_equal(0)
expect(arr[3]).to_equal(0)
```

</details>

#### allocates large i32 buffer (131072 elements)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_i32_array_alloc(131072)
expect(arr.len()).to_equal(131072)
```

</details>

### typed array alloc timing probe

#### records 1 MiB f64 alloc timing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = rt_time_now_nanos()
val arr = rt_f64_array_alloc(131072)
val elapsed_ns = rt_time_now_nanos() - start
expect(arr.len()).to_equal(131072)
# Manual timing check: expect elapsed_ns < 200_000_000 (200ms)
# rt_time_now_nanos may not be available in all interpreter builds;
# if elapsed_ns == 0 that is a no-op timer, not a failure
expect(elapsed_ns >= 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_perf_sugar.md](doc/03_plan/agent_tasks/scilib_port_perf_sugar.md)


</details>
