# SciPy Special Facade Specification

> Validates a first special-function facade.

<!-- sdn-diagram:id=scipy_special_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scipy_special_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scipy_special_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scipy_special_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Special Facade Specification

Validates a first special-function facade.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-special-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/scipy_special_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first special-function facade.

## Scenarios

### scipy.special erf_approx

#### returns zero at x=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(erf_approx(Float64.new(0.0))).to_equal(Float64.new(0.0))
```

</details>

#### is odd for mirrored inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = erf_approx(Float64.new(1.0))
val neg = erf_approx(Float64.new(-1.0))
expect(pos.value + neg.value < 0.000001).to_equal(true)
expect(pos.value + neg.value > -0.000001).to_equal(true)
```

</details>

#### is close to the common erf(1) reference value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = erf_approx(Float64.new(1.0)).value
expect(value > 0.8426).to_equal(true)
expect(value < 0.8428).to_equal(true)
```

</details>

### scipy.special integer helpers

#### computes factorial for non-negative values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(Int64.new(0)).unwrap()).to_equal(Int64.new(1))
expect(factorial(Int64.new(5)).unwrap()).to_equal(Int64.new(120))
```

</details>

#### computes combinations symmetrically

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(comb(Int64.new(5), Int64.new(2)).unwrap()).to_equal(Int64.new(10))
expect(comb(Int64.new(5), Int64.new(3)).unwrap()).to_equal(Int64.new(10))
expect(comb(Int64.new(6), Int64.new(0)).unwrap()).to_equal(Int64.new(1))
```

</details>

#### returns errors for invalid integer helper domains

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(Int64.new(-1)).is_err()).to_equal(true)
expect(comb(Int64.new(4), Int64.new(-1)).is_err()).to_equal(true)
expect(comb(Int64.new(4), Int64.new(5)).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)


</details>
