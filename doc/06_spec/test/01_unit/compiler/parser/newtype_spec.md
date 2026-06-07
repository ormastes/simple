# Newtype Specification

> <details>

<!-- sdn-diagram:id=newtype_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=newtype_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

newtype_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=newtype_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Newtype Specification

## Scenarios

### newtype wrapper

#### newtype creates constructible struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = Meters(value: 100)
expect(m.value).to_equal(100)
```

</details>

#### newtype value field is accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Celsius(value: 36.5)
expect(t.value).to_equal(36.5)
```

</details>

#### text newtype works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = Username(value: "alice")
expect(u.value).to_equal("alice")
```

</details>

#### newtype wraps a distinct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Meters(value: 5)
val b = Meters(value: 10)
expect(a.value + b.value).to_equal(15)
```

</details>

#### newtype fields can be updated

1. var m = Meters
   - Expected: m.value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = Meters(value: 1)
m.value = 42
expect(m.value).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/newtype_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- newtype wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
