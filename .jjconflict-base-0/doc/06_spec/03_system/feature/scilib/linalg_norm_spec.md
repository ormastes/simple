# Linalg Norm Specification

> Validates Euclidean vector norm behavior over the public linalg facade.

<!-- sdn-diagram:id=linalg_norm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linalg_norm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linalg_norm_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linalg_norm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg Norm Specification

Validates Euclidean vector norm behavior over the public linalg facade.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-linalg-norm |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/linalg_norm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates Euclidean vector norm behavior over the public linalg facade.

## Scenarios

### linalg.norm

#### computes the Euclidean norm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = vector_from([Float64.new(3.0), Float64.new(4.0)])
expect(norm(values)).to_equal(Float64.new(5.0))
```

</details>

#### returns zero for a zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = vector_from([Float64.new(0.0), Float64.new(0.0), Float64.new(0.0)])
expect(norm(values)).to_equal(Float64.new(0.0))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
