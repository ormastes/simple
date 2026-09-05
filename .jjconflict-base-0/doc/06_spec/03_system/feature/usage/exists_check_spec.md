# Existence Check Operator (.?) Specification

> The `.?` operator checks if a value is "present" (non-nil AND non-empty). Returns `T?` — the value itself if present, `nil` if absent.

<!-- sdn-diagram:id=exists_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=exists_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

exists_check_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=exists_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Existence Check Operator (.?) Specification

The `.?` operator checks if a value is "present" (non-nil AND non-empty). Returns `T?` — the value itself if present, `nil` if absent.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2100 |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | Implemented |
| Research | doc/01_research/text_validity_presence_pattern_2026-02-24.md |
| Source | `test/03_system/feature/usage/exists_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `.?` operator checks if a value is "present" (non-nil AND non-empty).
Returns `T?` — the value itself if present, `nil` if absent.

After compiler rebuild, `.?` returns `T?` instead of `bool`, enabling
pattern binding (`if val x = expr.?:`) and nil coalescing (`expr.? ?? default`).

## Behavior

- Option types: pass-through (Some stays Some, nil stays nil)
- Collections: returns value if non-empty, nil if empty
- Strings: returns value if non-empty, nil if ""
- Primitives: always returns value (0, false are still present)

## Related

- `presence(text) -> text?` — named equivalent for text
- `presence_trimmed(text) -> text?` — blank-aware variant

## Scenarios

### Existence Check Operator .?

#### Option type

#### returns true for Some

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val some_val: Option<i32> = Some(42)
expect some_val.? == true
```

</details>

#### returns true for Some(0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val some_zero: Option<i32> = Some(0)
expect some_zero.? == true
```

</details>

#### returns false for None

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val none_val: Option<i32> = None
expect none_val.? == false
```

</details>

#### List type

#### returns false for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: List<i32> = []
expect empty.? == false
```

</details>

#### returns true for non-empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3]
expect items.? == true
```

</details>

#### Dict type

#### returns false for empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: Dict<text, i32> = {}
expect empty.? == false
```

</details>

#### returns true for non-empty dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = {"a": 1}
expect items.? == true
```

</details>

#### String type

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = ""
expect empty.? == false
```

</details>

#### returns true for non-empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect s.? == true
```

</details>

#### Primitive types

#### returns true for positive number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val num = 42
expect num.? == true
```

</details>

#### returns true for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = 0
expect zero.? == true
```

</details>

#### returns true for false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = false
expect flag.? == true
```

</details>

#### with no-paren method calls

#### works with list.first.?

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3]
expect items.first.? == true
```

</details>

#### returns false for empty list.first.?

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: List<i32> = []
expect empty.first.? == false
```

</details>

#### works with string.trim.?

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "  hello  "
expect s.trim.? == true
```

</details>

#### works with chained no-paren methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "  HELLO  "
expect s.trim.lower.? == true
```

</details>

#### returns false for empty result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = ""
expect empty.trim.? == false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** [doc/01_research/text_validity_presence_pattern_2026-02-24.md](doc/01_research/text_validity_presence_pattern_2026-02-24.md)


</details>
