# Format Spec Specification

> <details>

<!-- sdn-diagram:id=format_spec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=format_spec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

format_spec_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=format_spec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Format Spec Specification

## Scenarios

### string format specifiers

#### basic string interpolation works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 42
val s = "value is {n}"
expect(s).to_equal("value is 42")
```

</details>

#### float interpolation works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pi = 3.14159
val s = "pi is {pi}"
expect(s).to_contain("3.14")
```

</details>

#### bool interpolation works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = true
val s = "flag={flag}"
expect(s).to_equal("flag=true")
```

</details>

#### text interpolation works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val greeting = "Hello, {name}!"
expect(greeting).to_equal("Hello, Alice!")
```

</details>

#### expression interpolation works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val s = "result={x * 2}"
expect(s).to_equal("result=10")
```

</details>

#### multiple interpolations in one string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 3
val b = 4
val s = "{a} + {b} = {a + b}"
expect(s).to_equal("3 + 4 = 7")
```

</details>

#### closing brace escaped with double brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 99
val s = "{n}}remaining"
# }} → literal }, result is "99}remaining"
expect(s).to_equal("99}remaining")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/format_spec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- string format specifiers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
