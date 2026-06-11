# Ce Syntax Specification

> <details>

<!-- sdn-diagram:id=ce_syntax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ce_syntax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ce_syntax_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ce_syntax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ce Syntax Specification

## Scenarios

### ce block syntax

### basic ce block as expression

#### ce block returns last value (concept)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 20
val result = x + y
expect(result).to_equal(30)
```

</details>

#### ce block with plain statements works (concept)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var side = 0
side = 7
val result = side * 3
expect(result).to_equal(21)
expect(side).to_equal(7)
```

</details>

### bind statement in ce block

#### bind stores non-nil value (concept)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = "hello"
val result = x.len()
expect(result).to_equal(5)
```

</details>

#### bind chains two values (concept)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 20
val result = x + y
expect(result).to_equal(30)
```

</details>

#### bind with nil short-circuits (concept)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reached = false
val x = nil
if x != nil:
    reached = true
expect(reached).to_equal(false)
```

</details>

#### bind result is nil when short-circuited (concept)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
var result = nil
if x != nil:
    result = "never"
expect(result).to_be_nil()
```

</details>

### bind with non-nil values passes through

#### bind passes text value (concept)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val result = "Hello, {name}!"
expect(result).to_equal("Hello, Alice!")
```

</details>

#### bind passes integer value (concept)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 42
val result = n * 2
expect(result).to_equal(84)
```

</details>

### nested ce blocks

#### nested ce blocks work independently (concept)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val inner = a + 1
val outer = inner * 10
expect(outer).to_equal(60)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/ce_syntax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ce block syntax
- basic ce block as expression
- bind statement in ce block
- bind with non-nil values passes through
- nested ce blocks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
