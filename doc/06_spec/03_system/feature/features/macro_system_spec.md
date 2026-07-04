# macro_system_spec

> Macro system core functionality specification.

<!-- sdn-diagram:id=macro_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_system_spec

Macro system core functionality specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Macro system core functionality specification.

Tests comprehensive macro system features including basic expansion,
hygienic variable handling, template substitution, and const-eval integration.

## Scenarios

### Macro System

### Basic macro expansion

#### expands simple expression macros

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = sys_ten!()
expect(x).to_equal(10)
```

</details>

#### expands macros with const parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = sys_multiply!(6, 7)
expect(x).to_equal(42)
```

</details>

#### handles multiple macro invocations independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = sys_counter!()
val second = sys_counter!()
val third = sys_counter!()
expect(first + second + third).to_equal(3)
```

</details>

### Hygienic expansion

#### prevents variable capture from outer scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let x = 5
val result = sys_make_ten!()
# Outer x should be 5, macro's x should be 10
expect(x + result).to_equal(15)
```

</details>

#### generates unique names for repeated expansions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = sys_increment!()
val b = sys_increment!()
# Each invocation has isolated temp
expect(a + b).to_equal(2)
```

</details>

### Template substitution

#### substitutes templates in identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = sys_get_value()
expect(x).to_equal(42)
```

</details>

#### substitutes templates in function names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = sys_my_adder(32)
expect(x).to_equal(42)
```

</details>

### Const-eval engine

#### evaluates arithmetic in const context

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = sys_add_three!(10, 20, 12)
expect(x).to_equal(42)
```

</details>

#### evaluates conditionals in const context

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sys_max!(10, 20)).to_equal(20)
expect(sys_max!(30, 5)).to_equal(30)
```

</details>

<details>
<summary>Advanced: evaluates loops in const context</summary>

#### evaluates loops in const context

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = sys_get_loop_0() + sys_get_loop_1() + sys_get_loop_2()
expect(sum).to_equal(3)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
