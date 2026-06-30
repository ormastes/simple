# Patchset Specification

> 1. expect true  # op target id

<!-- sdn-diagram:id=patchset_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=patchset_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

patchset_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=patchset_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Patchset Specification

## Scenarios

### PatchOp

#### identifies target node

1. expect true  # op target id


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # op.target_id() returns the node being patched
```

</details>

#### identifies target node for attr operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # SetAttr, RemoveAttr have node_id
```

</details>

#### identifies structural operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # InsertChild, RemoveChild, MoveChild are structural
```

</details>

#### identifies remove and move as structural

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # RemoveChild, ReplaceChild, MoveChild are structural
```

</details>

### PatchSet

#### starts empty

1. expect true  # PatchSet new


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # PatchSet.new().is_empty() == true
```

</details>

#### adds patches

1. expect true  # ps set text


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # ps.set_text(...); ps.len() == 1
```

</details>

#### provides helper methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # set_text, set_attr, add_class, remove_class
```

</details>

#### clears all patches

1. expect true  # ps clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # ps.clear(); ps.is_empty() == true
```

</details>

#### extends with multiple operations

1. expect true  # ps extend


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # ps.extend([op1, op2, op3])
```

</details>

#### supports insert and remove child helpers

1. expect true  # ps insert child


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # ps.insert_child(), ps.remove_child()
```

</details>

#### supports focus and event helpers

1. expect true  # ps focus


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # ps.focus(), ps.bind_event()
```

</details>

### PatchSet optimization

#### removes redundant text updates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # multiple set_text -> keep only last
```

</details>

#### removes redundant attr updates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # multiple set_attr for same -> keep only last
```

</details>

#### preserves structural operations order

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # insert order matters, don't reorder
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/patchset_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PatchOp
- PatchSet
- PatchSet optimization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
