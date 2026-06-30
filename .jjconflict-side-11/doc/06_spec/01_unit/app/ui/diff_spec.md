# Diff Specification

> 1. expect true  # diff

<!-- sdn-diagram:id=diff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diff_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diff Specification

## Scenarios

### diff

#### returns empty patches for identical trees

1. expect true  # diff


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # diff(elem, elem.clone()) -> empty patches
```

</details>

#### detects text changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # old "Hello" vs new "World" -> SetText patch
```

</details>

#### detects attribute additions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # old no attr vs new with_attr -> SetAttr patch
```

</details>

#### detects attribute removals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # old with_attr vs new no attr -> RemoveAttr patch
```

</details>

#### detects attribute changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # old attr="a" vs new attr="b" -> SetAttr patch
```

</details>

#### detects class additions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # old no class vs new with_class -> AddClass patch
```

</details>

#### detects class removals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # old with_class vs new no class -> RemoveClass patch
```

</details>

#### detects focus changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # old unfocused vs new focused -> SetFocus patch
```

</details>

### diff children

#### handles empty children

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # both empty -> no patches
```

</details>

#### detects new children

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # old empty vs new with child -> InsertChild patch
```

</details>

#### detects removed children

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # old with child vs new empty -> RemoveChild patch
```

</details>

#### matches keyed children

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # keyed reordering -> MoveChild patches
```

</details>

#### handles child updates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # child text changed -> SetText patch
```

</details>

### DiffResult

#### provides patches accessor

1. expect true  # result patches


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # result.patches()
```

</details>

#### allows taking patches

1. expect true  # result take patches


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # result.take_patches()
```

</details>

### ChildSnapshot

#### creates snapshot from element

1. expect true  # ChildSnapshot from element


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # ChildSnapshot.from_element(&elem)
```

</details>

#### creates snapshot without key

1. expect true  # elem without key -> snapshot key is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # elem without key -> snapshot.key.is_none()
```

</details>

### snapshot_children

#### creates snapshots from children array

1. expect true  # snapshot children


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # snapshot_children(&[a, b, c])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/diff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- diff
- diff children
- DiffResult
- ChildSnapshot
- snapshot_children

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
