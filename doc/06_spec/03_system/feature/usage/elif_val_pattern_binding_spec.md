# Elif Val/Var Pattern Binding Specification

> Tests for `elif val`/`elif var` pattern binding in conditional branches. Verifies that pattern matching works correctly in elif positions, matching the existing `if val` support.

<!-- sdn-diagram:id=elif_val_pattern_binding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=elif_val_pattern_binding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

elif_val_pattern_binding_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=elif_val_pattern_binding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elif Val/Var Pattern Binding Specification

Tests for `elif val`/`elif var` pattern binding in conditional branches. Verifies that pattern matching works correctly in elif positions, matching the existing `if val` support.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1001 |
| Category | Language |
| Status | Implemented |
| Source | `test/03_system/feature/usage/elif_val_pattern_binding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `elif val`/`elif var` pattern binding in conditional branches.
Verifies that pattern matching works correctly in elif positions,
matching the existing `if val` support.

## Syntax

```simple
if val Some(x) = expr1:
use(x)
elif val Some(y) = expr2:
use(y)
elif condition:
fallback()
else:
default()
```

## Scenarios

### Elif Val Pattern Binding

#### basic elif val matching

#### matches elif val when if condition is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(42)
var result = ""
if false:
    result = "if"
elif val Some(n) = x:
    result = "elif={n}"
expect result == "elif=42"
```

</details>

#### skips elif val when pattern does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = "default"
if false:
    result = "if"
elif val Some(n) = None:
    result = "elif={n}"
expect result == "default"
```

</details>

#### binds variable from elif val pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = Some("hello")
var captured = ""
if false:
    pass
elif val Some(s) = data:
    captured = s
expect captured == "hello"
```

</details>

#### elif val with else fallback

#### falls to else when elif val does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
if false:
    result = "if"
elif val Some(n) = None:
    result = "elif"
else:
    result = "else"
expect result == "else"
```

</details>

#### does not reach else when elif val matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
if false:
    result = "if"
elif val Some(n) = Some(99):
    result = "elif={n}"
else:
    result = "else"
expect result == "elif=99"
```

</details>

#### multiple elif val branches

#### matches first elif val pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Some(1)
val b = Some(2)
var result = ""
if false:
    result = "if"
elif val Some(n) = a:
    result = "first={n}"
elif val Some(n) = b:
    result = "second={n}"
expect result == "first=1"
```

</details>

#### matches second elif val when first does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = Some(2)
var result = ""
if false:
    result = "if"
elif val Some(n) = None:
    result = "first={n}"
elif val Some(n) = b:
    result = "second={n}"
expect result == "second=2"
```

</details>

#### falls through all elif val when none match

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = "none"
if false:
    result = "if"
elif val Some(n) = None:
    result = "first"
elif val Some(n) = None:
    result = "second"
expect result == "none"
```

</details>

#### mixed elif and elif val

#### matches regular elif before elif val

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
if false:
    result = "if"
elif true:
    result = "elif-bool"
elif val Some(n) = Some(42):
    result = "elif-val"
expect result == "elif-bool"
```

</details>

#### matches elif val after failed regular elif

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(10)
var result = ""
if false:
    result = "if"
elif false:
    result = "elif-bool"
elif val Some(n) = x:
    result = "elif-val={n}"
expect result == "elif-val=10"
```

</details>

#### matches regular elif after failed elif val

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
if false:
    result = "if"
elif val Some(n) = None:
    result = "elif-val"
elif true:
    result = "elif-bool"
expect result == "elif-bool"
```

</details>

#### reaches else after mixed elif failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
if false:
    result = "if"
elif false:
    result = "elif-bool"
elif val Some(n) = None:
    result = "elif-val"
else:
    result = "else"
expect result == "else"
```

</details>

#### if val combined with elif val

#### matches if val and skips elif val

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
if val Some(n) = Some(1):
    result = "if={n}"
elif val Some(n) = Some(2):
    result = "elif={n}"
expect result == "if=1"
```

</details>

#### skips if val and matches elif val

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
if val Some(n) = None:
    result = "if"
elif val Some(n) = Some(2):
    result = "elif={n}"
expect result == "elif=2"
```

</details>

#### skips both if val and elif val to else

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
if val Some(n) = None:
    result = "if"
elif val Some(n) = None:
    result = "elif"
else:
    result = "else"
expect result == "else"
```

</details>

#### nested option patterns

#### matches nested Some in elif val

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = Some(Some(99))
var result = ""
if val Some(Some(n)) = None:
    result = "none"
elif val Some(Some(n)) = inner:
    result = "nested={n}"
expect result == "nested=99"
```

</details>

#### chains multiple Some patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = None
val b = None
val c = Some(7)
var result = ""
if val Some(x) = a:
    result = "a={x}"
elif val Some(x) = b:
    result = "b={x}"
elif val Some(x) = c:
    result = "c={x}"
else:
    result = "none"
expect result == "c=7"
```

</details>

#### elif val as implicit return

#### returns from elif val branch

1. fn classify
2. expect classify
3. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(opt):
    if val Some(n) = None:
        "none-matched"
    elif val Some(n) = opt:
        "got={n}"
    else:
        "nothing"

expect classify(Some(7)) == "got=7"
expect classify(None) == "nothing"
```

</details>

#### elif val scope isolation

#### bindings do not leak to outer scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var outer = "unchanged"
if val Some(n) = None:
    pass
elif val Some(n) = Some(42):
    outer = "n={n}"
# n should not be accessible here
expect outer == "n=42"
```

</details>

#### elif val with nil/no-match returns nil

#### returns nil when no branch matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = "before"
if false:
    result = "if"
elif val Some(n) = None:
    result = "elif"
# No else - should just continue
expect result == "before"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
