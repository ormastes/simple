# Replay Feature Registry Specification

> <details>

<!-- sdn-diagram:id=replay_feature_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_feature_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_feature_registry_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_feature_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Feature Registry Specification

## Scenarios

### Replay FeatureId round-trip (to_i32 -> from_i32)

#### RecordStart round-trips through i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feat = FeatureId::RecordStart
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("RecordStart")
```

</details>

#### RecordStop round-trips through i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feat = FeatureId::RecordStop
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("RecordStop")
```

</details>

#### ReplayStart round-trips through i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feat = FeatureId::ReplayStart
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("ReplayStart")
```

</details>

#### ReplayStop round-trips through i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feat = FeatureId::ReplayStop
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("ReplayStop")
```

</details>

#### ReverseFinish round-trips through i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feat = FeatureId::ReverseFinish
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("ReverseFinish")
```

</details>

#### ReverseWatch round-trips through i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feat = FeatureId::ReverseWatch
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("ReverseWatch")
```

</details>

#### CheckpointSave round-trips through i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feat = FeatureId::CheckpointSave
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("CheckpointSave")
```

</details>

#### CheckpointRestore round-trips through i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feat = FeatureId::CheckpointRestore
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("CheckpointRestore")
```

</details>

### Replay FeatureId to_text

#### RecordStart to_text returns correct string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(FeatureId::RecordStart.to_text()).to_equal("RecordStart")
```

</details>

#### CheckpointRestore to_text returns correct string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(FeatureId::CheckpointRestore.to_text()).to_equal("CheckpointRestore")
```

</details>

### Replay FeatureId edge cases

#### from_i32 with invalid ID returns default (Halt)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feat = FeatureId.from_i32(9999)
expect(feat.to_string()).to_equal("Halt")
```

</details>

#### all 8 replay variants have distinct IDs

1. FeatureId::RecordStart to i32
2. FeatureId::RecordStop to i32
3. FeatureId::ReplayStart to i32
4. FeatureId::ReplayStop to i32
5. FeatureId::ReverseFinish to i32
6. FeatureId::ReverseWatch to i32
7. FeatureId::CheckpointSave to i32
8. FeatureId::CheckpointRestore to i32
   - Expected: all_distinct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ids = [
    FeatureId::RecordStart.to_i32(),
    FeatureId::RecordStop.to_i32(),
    FeatureId::ReplayStart.to_i32(),
    FeatureId::ReplayStop.to_i32(),
    FeatureId::ReverseFinish.to_i32(),
    FeatureId::ReverseWatch.to_i32(),
    FeatureId::CheckpointSave.to_i32(),
    FeatureId::CheckpointRestore.to_i32()
]
# Verify no duplicates by checking each pair
var all_distinct = true
for i in 0..ids.len():
    for j in (i + 1)..ids.len():
        if ids[i] == ids[j]:
            all_distinct = false
expect(all_distinct).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_feature_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Replay FeatureId round-trip (to_i32 -> from_i32)
- Replay FeatureId to_text
- Replay FeatureId edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
