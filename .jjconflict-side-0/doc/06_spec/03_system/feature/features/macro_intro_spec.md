# macro_intro_spec

> Macro intro contracts specification.

<!-- sdn-diagram:id=macro_intro_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_intro_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_intro_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_intro_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_intro_spec

Macro intro contracts specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_intro_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Macro intro contracts specification.

Tests function introduction via macros including simple function generation,
parameterized functions, loop-based generation, and template substitution.

## Scenarios

### Intro Contracts

### Simple function introduction

#### generates functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = intro_add_n(32)
expect(x).to_equal(42)
```

</details>

#### generates functions with parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(intro_multiply(7)).to_equal(42)
```

</details>

### Multiple function generation

<details>
<summary>Advanced: generates axis functions from loop</summary>

#### generates axis functions from loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = intro_get_axis_0() + intro_get_axis_1() + intro_get_axis_2()
expect(sum).to_equal(3)
```

</details>


</details>

#### generates multiple named functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(intro_get_first() + intro_get_second()).to_equal(42)
```

</details>

### Template substitution in names

#### generates getter functions with string values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(intro_get_value()).to_equal(42)
```

</details>

#### generates checker functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(intro_check_positive()).to_equal(true)
expect(intro_check_negative()).to_equal(false)
```

</details>

### Combined intro patterns

#### generates accessor pair with template

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(intro_prop_get_data()).to_equal(42)
expect(intro_prop_set_data(100)).to_equal(100)
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


</details>
