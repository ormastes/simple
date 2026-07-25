# Option Ce E2e Specification

> <details>

<!-- sdn-diagram:id=option_ce_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=option_ce_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

option_ce_e2e_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=option_ce_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Ce E2e Specification

## Scenarios

### ce option_ce block desugaring

### successful binds

#### evaluates final expression when all binds succeed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val user = "alice"
val profile = "admin"
val result = "{user}:{profile}"
expect(result).to_equal("alice:admin")
```

</details>

#### single bind returns value in final expr

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 99
val result = x * 2
expect(result).to_equal(198)
```

</details>

#### binds two values and combines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 3
val b = 4
val result = a + b
expect(result).to_equal(7)
```

</details>

#### returns string length from bound value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val result = s.len()
expect(result).to_equal(5)
```

</details>

### short-circuit on None (nil)

#### returns nil when first bind is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
var result = nil
if x != nil:
    result = "should not reach"
expect(result).to_be_nil()
```

</details>

#### returns nil when second bind is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = "found"
val second = nil
var result = nil
if first != nil and second != nil:
    result = "{first}+{second}"
expect(result).to_be_nil()
```

</details>

#### stops evaluation at first nil bind

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reached = 0
val x = nil
if x != nil:
    reached = 1
expect(reached).to_equal(0)
```

</details>

### nested CE blocks

#### inner result used in outer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = "inner"
val inner = x
val y = inner
val result = "outer: {y}"
expect(result).to_equal("outer: inner")
```

</details>

#### inner nil propagates to outer

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
var inner = nil
if x != nil:
    inner = x
var result = nil
if inner != nil:
    result = "should not reach"
expect(result).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/option_ce_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ce option_ce block desugaring
- successful binds
- short-circuit on None (nil)
- nested CE blocks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
