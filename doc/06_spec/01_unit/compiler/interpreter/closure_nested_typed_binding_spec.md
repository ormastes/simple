# Closure Nested Typed Binding Specification

> <details>

<!-- sdn-diagram:id=closure_nested_typed_binding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=closure_nested_typed_binding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

closure_nested_typed_binding_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=closure_nested_typed_binding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Closure Nested Typed Binding Specification

## Scenarios

### typed val bindings in nested closure blocks

#### binds annotated i32 inside if and reads it

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond = true
if cond:
    val x: i32 = 5
    expect(x).to_equal(5)
else:
    expect(2).to_equal(2)
```

</details>

#### binds annotated u32 inside if and passes it as call arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond = true
if cond:
    val v: u32 = 0xFF0000FFu32
    expect(take_u(v)).to_equal(0xFF0000FFu32)
else:
    expect(2).to_equal(2)
```

</details>

#### binds annotated val inside while body

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
var total = 0
while i < 1:
    val x: i32 = 7
    total = total + x
    i = i + 1
expect(total).to_equal(7)
```

</details>

#### binds annotated val inside else branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond = false
if cond:
    expect(1).to_equal(1)
else:
    val x: i32 = 9
    expect(x).to_equal(9)
```

</details>

#### binds tuple destructuring inside if

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond = true
if cond:
    val (a, b) = (3, 4)
    expect(a + b).to_equal(7)
else:
    expect(2).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/closure_nested_typed_binding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- typed val bindings in nested closure blocks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
