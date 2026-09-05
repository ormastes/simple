# macro_templates_spec

> Macro template substitution specification.

<!-- sdn-diagram:id=macro_templates_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_templates_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_templates_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_templates_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_templates_spec

Macro template substitution specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_templates_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Macro template substitution specification.

Tests template substitution in macros including string interpolation,
dynamic function name generation, and identifier templating.

## Scenarios

### Template Substitution

### Templates in function names

#### generates functions with template names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = tpl_get_value()
expect(x).to_equal(42)
```

</details>

#### generates operation functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = tpl_math_op_adder(32)
expect(x).to_equal(42)
```

</details>

### Templates with for loops

<details>
<summary>Advanced: generates multiple functions with loop index</summary>

#### generates multiple functions with loop index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = tpl_loop_get_0() + tpl_loop_get_1() + tpl_loop_get_2()
expect(sum).to_equal(3)
```

</details>


</details>

### Templates with numbers

#### combines strings and numbers in names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = tpl_add_num_10(32)
expect(x).to_equal(42)
```

</details>

### Template intro with const param

#### uses const parameter in intro name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = tpl_custom_v2_adder(32)
expect(x).to_equal(42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
