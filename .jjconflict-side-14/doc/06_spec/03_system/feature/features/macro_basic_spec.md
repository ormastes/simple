# macro_basic_spec

> Basic macro system specification.

<!-- sdn-diagram:id=macro_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_basic_spec

Basic macro system specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Basic macro system specification.

Tests fundamental macro functionality including simple expression macros,
const parameter passing, and template-based code generation.

## Scenarios

### Basic Macros

#### expands simple macro

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = basic_answer!()
expect(x).to_equal(42)
```

</details>

#### uses const parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = basic_double!(21)
expect(x).to_equal(42)
```

</details>

#### generates function with template

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = basic_add!(30, 12)
expect(x).to_equal(42)
```

</details>

#### evaluates max correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = basic_max!(10, 50)
expect(x).to_equal(50)

val y = basic_max!(100, 5)
expect(y).to_equal(100)
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


</details>
