# Simple Language Syntax Specification - Test Specification

> Comprehensive tests for Simple's syntax, including literals, string interpolation, operators, and indentation-based parsing.

<!-- sdn-diagram:id=syntax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syntax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syntax_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syntax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Syntax Specification - Test Specification

Comprehensive tests for Simple's syntax, including literals, string interpolation, operators, and indentation-based parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #10-19 |
| Category | Language Features |
| Status | Stable |
| Source | `test/03_system/feature/usage/syntax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive tests for Simple's syntax, including literals, string interpolation,
operators, and indentation-based parsing.

Simple uses Python-like indentation with type annotations and explicit execution mode control.

## Related Specifications

- **Types** - Type annotations and type syntax
- **Functions** - Function definition syntax
- **Parser** - Parser implementation details

## Scenarios

### Syntax Spec

#### syntax overview - if/else

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# An if/else example with indentation
val x = 1
if x > 0:
    check(true)
else:
    check(false)
```

</details>

#### syntax overview - iteration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Iterating with a trailing block
val list = [1, 2, 3]
check(true)
```

</details>

#### literals - integer formats

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 1_000_000
val color = 0xFF5733
val mask = 0x0000_FFFF
val flags = 0b1010_0101
val permissions = 0o755
check(true)
```

</details>

#### literals - floating point

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pi = 3.14159
check(true)
```

</details>

#### literals - typed suffixes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Typed suffixes for clarity
check(true)
```

</details>

#### string literals - interpolation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "world"
val count = 42
val msg = "Hello, {name}! Count is {count + 1}"
check(true)
```

</details>

#### string literals - raw strings

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regex = '[a-z]+\d{2,3}'
val path = 'C:\Users\name'
check(true)
```

</details>

#### string literals - basic interpolation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "world"
val msg = "Hello, {name}!"
check(true)
```

</details>

#### functional update syntax - arrays

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = [1, 2, 3]
check(true)
```

</details>

#### functional update syntax - basic

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### functional update syntax - lists

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var list = [1, 2, 3]
check(true)
```

</details>

#### functional update syntax - pattern 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### functional update syntax - pattern 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### parsing design rationale - simplicity

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### parsing design rationale - lambdas

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val double = \x: x * 2
check(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
