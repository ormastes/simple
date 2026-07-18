# Linalg Trace Specification

> Validates matrix trace behavior over the public linalg facade.

<!-- sdn-diagram:id=linalg_trace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linalg_trace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linalg_trace_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linalg_trace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg Trace Specification

Validates matrix trace behavior over the public linalg facade.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-linalg-trace |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/linalg_trace_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates matrix trace behavior over the public linalg facade.

## Scenarios

### linalg.trace

<details>
<summary>Advanced: sums the diagonal of a square matrix</summary>

#### sums the diagonal of a square matrix

1. [Float64 new
2. [Float64 new
   - Expected: trace(a).unwrap() equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)]])
expect(trace(a).unwrap()).to_equal(Float64.new(5.0))
```

</details>


</details>

#### uses the shorter diagonal for rectangular matrices

1. [Float64 new
2. [Float64 new
   - Expected: trace(a).unwrap() equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
expect(trace(a).unwrap()).to_equal(Float64.new(6.0))
```

</details>

<details>
<summary>Advanced: returns errors for non-matrix and unsupported dtype inputs</summary>

#### returns errors for non-matrix and unsupported dtype inputs

1. Shape new
   - Expected: trace(ints).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(trace(vector_from([Float64.new(1.0), Float64.new(2.0)])).is_err()).to_equal(true)
val ints = array_i64([Int64.new(1), Int64.new(2), Int64.new(3), Int64.new(4)]).reshape(
    Shape.new([Index.new(2), Index.new(2)])
)
expect(trace(ints).is_err()).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
