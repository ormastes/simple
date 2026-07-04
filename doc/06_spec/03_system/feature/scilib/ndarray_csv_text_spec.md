# NDArray CSV Text Specification

> Validates pure CSV text import/export for 1D and 2D Float64 arrays.

<!-- sdn-diagram:id=ndarray_csv_text_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_csv_text_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_csv_text_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_csv_text_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray CSV Text Specification

Validates pure CSV text import/export for 1D and 2D Float64 arrays.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-array-io |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/ndarray_csv_text_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates pure CSV text import/export for 1D and 2D Float64 arrays.

## Scenarios

### NDArray CSV text I/O

#### parses one-line CSV text as a 1D Float64 array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array_from_csv_text("1.5,2.5,-3.0").unwrap()
expect(values.shape).to_equal(Shape.new([Index.new(3)]))
expect(values.flat_f64(0)).to_equal(Float64.new(1.5))
expect(values.flat_f64(2)).to_equal(Float64.new(-3.0))
```

</details>

#### parses multi-line CSV text as a 2D Float64 array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array_from_csv_text("1.0,2.0\n3.0,4.0").unwrap()
expect(values.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(values.get_f64_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.0))
expect(values.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(4.0))
```

</details>

#### exports arrays to CSV text and parses them back

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]).reshape(Shape.new([Index.new(1), Index.new(3)]))
val csv = values.to_csv_text().unwrap()
val parsed = array_from_csv_text(csv).unwrap()
expect(parsed.shape).to_equal(Shape.new([Index.new(3)]))
expect(parsed.flat_f64(2)).to_equal(Float64.new(3.0))
```

</details>

#### returns errors for malformed and unsupported arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_from_csv_text("").is_err()).to_equal(true)
expect(array_from_csv_text("1.0,2.0\n3.0").is_err()).to_equal(true)
expect(array_from_csv_text("nope").is_err()).to_equal(true)
expect(array_i64([Int64.new(1)]).to_csv_text().is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
