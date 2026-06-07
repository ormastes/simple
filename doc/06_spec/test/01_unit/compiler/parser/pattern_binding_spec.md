# Pattern Binding Specification

> <details>

<!-- sdn-diagram:id=pattern_binding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pattern_binding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pattern_binding_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pattern_binding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pattern Binding Specification

## Scenarios

### pattern binding in match

#### matched value used via original variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val result = match x:
    case 42: x * 2
    case _: 0
expect(result).to_equal(84)
```

</details>

#### match with guard uses enclosing scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val result = match x:
    case 10 if x > 5: "big"
    case _: "small"
expect(result).to_equal("big")
```

</details>

#### wildcard works without binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 99
val result = match x:
    case 42: "forty-two"
    case _: "other"
expect(result).to_equal("other")
```

</details>

#### string pattern matched via function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_word("hello")
expect(result).to_equal("hello world")
```

</details>

#### extract function uses matched literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = extract_number(10)
expect(result).to_equal(15)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/pattern_binding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pattern binding in match

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
