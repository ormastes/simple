# macro_hygiene_spec

> Macro hygiene specification.

<!-- sdn-diagram:id=macro_hygiene_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_hygiene_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_hygiene_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_hygiene_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_hygiene_spec

Macro hygiene specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_hygiene_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Macro hygiene specification.

Tests that macro-generated variables are properly isolated through
gensym renaming, preventing unintended variable capture from outer scopes.

## Scenarios

### Macro Hygiene

#### prevents variable capture from outer scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let x = 5
val result = hyg_make_ten!()
# Should be 5 + 10 = 15, not 10 + 10 = 20
expect(x + result).to_equal(15)
```

</details>

#### generates unique names for repeated expansions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = hyg_increment!()
val b = hyg_increment!()
expect(a + b).to_equal(2)
```

</details>

#### allows explicit shadowing with different values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hyg_shadow_test!()
# ((10 + 5) * 2) = 30
expect(result).to_equal(30)
```

</details>

#### isolates macro-generated variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let x = 10
let y = 20
let z = 30
val result = hyg_multi_vars!()
# 10 + 20 + 30 + 6 = 66
expect(x + y + z + result).to_equal(66)
```

</details>

#### maintains hygiene with nested macro calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = hyg_outer!()
# Should be 10 + 5 = 15
expect(result).to_equal(15)
```

</details>

#### isolates pattern matching variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let x = 100
let y = 200
val result = hyg_make_pair!()
# 100 + 200 + 30 = 330
expect(x + y + result).to_equal(330)
```

</details>

#### isolates tuple destructuring

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let a = 1
let b = 2
val result = hyg_swap_values!()
# 1 + 2 + 5 = 8
expect(a + b + result).to_equal(8)
```

</details>

#### handles complex macro with multiple scopes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let x = 100
let y = 200
let z = 300
val result = hyg_complex!()
expect(result).to_equal(10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
