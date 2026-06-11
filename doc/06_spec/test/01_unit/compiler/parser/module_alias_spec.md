# Module Alias Specification

> <details>

<!-- sdn-diagram:id=module_alias_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_alias_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_alias_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_alias_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Alias Specification

## Scenarios

### module aliasing

#### delegation pattern provides function aliasing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = double(5)
expect(result).to_equal(10)
```

</details>

#### multiple delegation aliases work independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = double(4)
val t = triple(4)
expect(d).to_equal(8)
expect(t).to_equal(12)
```

</details>

#### type alias works for type-level aliasing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val len: Length = 42
expect(len).to_equal(42)
```

</details>

#### aliased function used in expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = double(3) + triple(2)
expect(x).to_equal(12)
```

</details>

#### aliased bool function works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = negate(true)
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/module_alias_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- module aliasing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
