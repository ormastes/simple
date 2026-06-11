# Associated Types Specification

> <details>

<!-- sdn-diagram:id=associated_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=associated_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

associated_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=associated_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Associated Types Specification

## Scenarios

### associated types

#### struct with associated type alias works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: ItemType = 42
expect(x).to_equal(42)
```

</details>

#### struct fields are accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = IntList(items: [1, 2, 3])
expect(list.size()).to_equal(3)
```

</details>

#### struct item access via type alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = IntList(items: [10, 20])
val item: ItemType = list.get(0)
expect(item).to_equal(10)
```

</details>

#### key type alias works with text struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key: KeyType = "hello"
expect(key.len()).to_equal(5)
```

</details>

#### struct with key/value works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TextMap(keys: ["a", "b"], values: ["1", "2"])
expect(m.count()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/associated_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- associated types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
