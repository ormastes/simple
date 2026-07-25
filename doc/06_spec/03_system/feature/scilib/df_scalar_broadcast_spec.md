# DataFrame Scalar Broadcast Specification

> Validates Series scalar broadcast methods: add_scalar, sub_scalar, mul_scalar, div_scalar.

<!-- sdn-diagram:id=df_scalar_broadcast_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_scalar_broadcast_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_scalar_broadcast_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_scalar_broadcast_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Scalar Broadcast Specification

Validates Series scalar broadcast methods: add_scalar, sub_scalar, mul_scalar, div_scalar.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-14, T-DF-15, science-math-lib-set-pandas-core-scalar-broadcast |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_scalar_broadcast_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates Series scalar broadcast methods: add_scalar, sub_scalar, mul_scalar, div_scalar.
No operator overloading sugar (PERF-SUGAR-003 risk) — explicit method calls only.

## Scenarios

### Series scalar broadcast

#### add_scalar adds rhs to each element

1. name: Symbol from
2. values: [Float64 new
   - Expected: result.get(Index.new(0)) equals `Float64.new(11.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(12.0)`
   - Expected: result.get(Index.new(2)) equals `Float64.new(13.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
)
val result = s.add_scalar(Float64.new(10.0))
expect(result.get(Index.new(0))).to_equal(Float64.new(11.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(12.0))
expect(result.get(Index.new(2))).to_equal(Float64.new(13.0))
```

</details>

#### add_scalar preserves series name

1. name: Symbol from
2. values: [Float64 new
   - Expected: result.name() equals `Symbol.from("x")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("x"),
    values: [Float64.new(5.0)]
)
val result = s.add_scalar(Float64.new(1.0))
expect(result.name()).to_equal(Symbol.from("x"))
```

</details>

#### sub_scalar subtracts rhs from each element

1. name: Symbol from
2. values: [Float64 new
   - Expected: result.get(Index.new(0)) equals `Float64.new(7.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(17.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("a"),
    values: [Float64.new(10.0), Float64.new(20.0)]
)
val result = s.sub_scalar(Float64.new(3.0))
expect(result.get(Index.new(0))).to_equal(Float64.new(7.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(17.0))
```

</details>

#### mul_scalar multiplies each element by rhs

1. name: Symbol from
2. values: [Float64 new
   - Expected: result.get(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(12.0)`
   - Expected: result.get(Index.new(2)) equals `Float64.new(18.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("b"),
    values: [Float64.new(2.0), Float64.new(4.0), Float64.new(6.0)]
)
val result = s.mul_scalar(Float64.new(3.0))
expect(result.get(Index.new(0))).to_equal(Float64.new(6.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(12.0))
expect(result.get(Index.new(2))).to_equal(Float64.new(18.0))
```

</details>

#### div_scalar divides each element by rhs

1. name: Symbol from
2. values: [Float64 new
   - Expected: result.get(Index.new(0)) equals `Float64.new(5.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(10.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("c"),
    values: [Float64.new(10.0), Float64.new(20.0)]
)
val result = s.div_scalar(Float64.new(2.0)).unwrap()
expect(result.get(Index.new(0))).to_equal(Float64.new(5.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(10.0))
```

</details>

#### div_scalar returns error when rhs is zero

1. name: Symbol from
2. values: [Float64 new
   - Expected: s.div_scalar(Float64.new(0.0)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("d"),
    values: [Float64.new(1.0)]
)
expect(s.div_scalar(Float64.new(0.0)).is_err()).to_equal(true)
```

</details>

#### add_scalar returns F64 dtype

1. name: Symbol from
2. values: [Float64 new
   - Expected: result.dtype() equals `DType.F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("e"),
    values: [Float64.new(1.0), Float64.new(2.0)]
)
val result = s.add_scalar(Float64.new(1.0))
expect(result.dtype()).to_equal(DType.F64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
