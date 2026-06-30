# NDArray Random Basics Specification

> Validates deterministic random vector generation for the first NumPy-random

<!-- sdn-diagram:id=ndarray_random_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_random_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_random_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_random_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Random Basics Specification

Validates deterministic random vector generation for the first NumPy-random

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-random-basics |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/ndarray_random_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates deterministic random vector generation for the first NumPy-random
slice. This is not a cryptographic RNG.

## Scenarios

### NDArray random_uniform

#### returns a deterministic Float64 vector for a seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = random_uniform(Int64.new(123), Index.new(3)).unwrap()
val b = random_uniform(Int64.new(123), Index.new(3)).unwrap()
expect(a.dtype).to_equal(DType.F64)
expect(a.shape).to_equal(Shape.new([Index.new(3)]))
expect(a.get(Index.new(0))).to_equal(b.get(Index.new(0)))
expect(a.get(Index.new(1))).to_equal(b.get(Index.new(1)))
expect(a.get(Index.new(2))).to_equal(b.get(Index.new(2)))
```

</details>

#### keeps generated values in the half-open range [0, 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = random_uniform(Int64.new(7), Index.new(4)).unwrap()
expect(a.min().value >= 0.0).to_equal(true)
expect(a.max().value < 1.0).to_equal(true)
```

</details>

#### returns an error for negative counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(random_uniform(Int64.new(1), Index.new(-1)).is_err()).to_equal(true)
```

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


</details>
