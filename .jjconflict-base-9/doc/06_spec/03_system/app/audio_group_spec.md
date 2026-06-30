# Audio Group Specification

> <details>

<!-- sdn-diagram:id=audio_group_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=audio_group_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

audio_group_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=audio_group_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audio Group Specification

## Scenarios

### AudioGroupTree — empty tree

#### new tree has no groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AudioGroupTree.new()
val g = tree.get_group("anything")
expect(g).to_be_nil()
```

</details>

### AudioGroupTree — add groups

#### add root group makes it retrievable

1. var tree = AudioGroupTree new
2. tree add group
   - Expected: g.name equals `master`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = AudioGroupTree.new()
tree.add_group("master", "")
val g = tree.get_group("master")
expect(g.name).to_equal("master")
```

</details>

#### add child group with correct parent

1. var tree = AudioGroupTree new
2. tree add group
3. tree add group
   - Expected: g.name equals `sfx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = AudioGroupTree.new()
tree.add_group("master", "")
tree.add_group("sfx", "master")
val g = tree.get_group("sfx")
expect(g.name).to_equal("sfx")
```

</details>

### AudioGroupTree — effective volume

#### parent 0.5 times child 0.8 equals 0.4

1. var tree = AudioGroupTree new
2. tree add group
3. tree add group
4. tree set volume
5. tree set volume
   - Expected: vol.value > 0.39 is true
   - Expected: vol.value < 0.41 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = AudioGroupTree.new()
tree.add_group("master", "")
tree.add_group("sfx", "master")
tree.set_volume("master", Volume(value: 0.5))
tree.set_volume("sfx", Volume(value: 0.8))
val vol = tree.get_effective_volume("sfx")
expect(vol.value > 0.39).to_equal(true)
expect(vol.value < 0.41).to_equal(true)
```

</details>

### AudioGroupTree — effective muted

#### mute parent makes child effectively muted

1. var tree = AudioGroupTree new
2. tree add group
3. tree add group
4. tree set muted
   - Expected: muted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = AudioGroupTree.new()
tree.add_group("master", "")
tree.add_group("sfx", "master")
tree.set_muted("master", true)
val muted = tree.get_effective_muted("sfx")
expect(muted).to_equal(true)
```

</details>

### AudioGroupTree — set volume

#### set_volume updates group volume

1. var tree = AudioGroupTree new
2. tree add group
3. tree set volume
   - Expected: vol.value > 0.69 is true
   - Expected: vol.value < 0.71 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = AudioGroupTree.new()
tree.add_group("master", "")
tree.set_volume("master", Volume(value: 0.7))
val vol = tree.get_effective_volume("master")
expect(vol.value > 0.69).to_equal(true)
expect(vol.value < 0.71).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/audio_group_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AudioGroupTree — empty tree
- AudioGroupTree — add groups
- AudioGroupTree — effective volume
- AudioGroupTree — effective muted
- AudioGroupTree — set volume

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
