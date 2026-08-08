# Existence Check Value Return (.? → T?) Specification

> After the `.?` return-type change, the operator returns `T?` instead of `bool`. This enables pattern binding (`if val x = expr.?:`) and nil coalescing (`expr.? ?? default`).

<!-- sdn-diagram:id=exists_check_value_return_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=exists_check_value_return_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

exists_check_value_return_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=exists_check_value_return_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Existence Check Value Return (.? → T?) Specification

After the `.?` return-type change, the operator returns `T?` instead of `bool`. This enables pattern binding (`if val x = expr.?:`) and nil coalescing (`expr.? ?? default`).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2100-VALUE-RETURN |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | Implemented (requires compiler rebuild) |
| Research | doc/01_research/text_validity_presence_pattern_2026-02-24.md |
| Source | `test/03_system/feature/usage/exists_check_value_return_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

After the `.?` return-type change, the operator returns `T?` instead of `bool`.
This enables pattern binding (`if val x = expr.?:`) and nil coalescing
(`expr.? ?? default`).

## Behavior

`.?` returns `T?` — value if present, nil if absent. Option types pass through
without double-wrapping. See `doc/06_spec/app/compiler/feature/exists_check_spec.md` for the
full type/return table.

## Related

- `exists_check_spec.spl` — boolean truthiness tests
- `elif_val_pattern_binding_spec.spl` — `if val` / `elif val` patterns

## Scenarios

### Existence Check Value Return (.? -> T?)

#### nil coalescing with text

#### returns value for non-empty string via ??

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val result = s.? ?? "default"
expect result == "hello"
```

</details>

#### returns default for empty string via ??

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
val result = s.? ?? "default"
expect result == "default"
```

</details>

#### chains multiple ?? fallbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ""
val b = ""
val c = "found"
val result = a.? ?? b.? ?? c.? ?? "none"
expect result == "found"
```

</details>

#### nil coalescing with collections

#### returns list for non-empty list via ??

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3]
val result = items.? ?? [0]
expect result == [1, 2, 3]
```

</details>

#### returns default for empty list via ??

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: List<i32> = []
val result = empty.? ?? [0]
expect result == [0]
```

</details>

#### pattern binding with if val

#### binds non-empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "hello"
var result = "unset"
if val name = input.?:
    result = name
expect result == "hello"
```

</details>

#### skips binding for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = ""
var result = "default"
if val name = input.?:
    result = name
expect result == "default"
```

</details>

#### binds non-empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [10, 20]
var result = "unset"
if val bound = items.?:
    result = "bound"
expect result == "bound"
```

</details>

#### skips binding for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: List<i32> = []
var result = "default"
if val bound = empty.?:
    result = "bound"
expect result == "default"
```

</details>

#### Option pass-through

#### passes through Some value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i32> = Some(42)
val result = opt.? ?? 0
expect result == 42
```

</details>

#### returns default for None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i32> = None
val result = opt.? ?? 0
expect result == 0
```

</details>

#### binds Some value with if val

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<text> = Some("hi")
var result = "unset"
if val s = opt.?:
    result = s
expect result == "hi"
```

</details>

#### primitive values

#### returns number via ??

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 42
val result = n.? ?? 0
expect result == 42
```

</details>

#### returns zero via ??

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 0
val result = n.? ?? -1
expect result == 0
```

</details>

#### chained with methods

#### works with trim and ??

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "  hello  "
val result = s.trim.? ?? "empty"
expect result == "hello"
```

</details>

#### returns default for empty trim result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
val result = s.trim.? ?? "empty"
expect result == "empty"
```

</details>

#### works with list.first and ??

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [42, 99]
val result = items.first.? ?? 0
expect result == 42
```

</details>

#### returns default for empty list.first

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: List<i32> = []
val result = empty.first.? ?? 0
expect result == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** [doc/01_research/text_validity_presence_pattern_2026-02-24.md](doc/01_research/text_validity_presence_pattern_2026-02-24.md)


</details>
