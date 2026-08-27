# Replay Feature Registry Specification

> Tests covering Replay FeatureId round-trip (to_i32 -> from_i32), Replay FeatureId to_text, Replay FeatureId edge cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Feature Registry Specification

## Scenarios

### Replay FeatureId round-trip (to_i32 -> from_i32)

#### RecordStart round-trips through i32

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- RecordStart round-trips through i32
   - Expected: back.to_string() equals `RecordStart`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("RecordStart round-trips through i32")
val feat = FeatureId::RecordStart
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("RecordStart")
```

</details>

#### RecordStop round-trips through i32

- RecordStop round-trips through i32
   - Expected: back.to_string() equals `RecordStop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("RecordStop round-trips through i32")
val feat = FeatureId::RecordStop
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("RecordStop")
```

</details>

#### ReplayStart round-trips through i32

- ReplayStart round-trips through i32
   - Expected: back.to_string() equals `ReplayStart`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ReplayStart round-trips through i32")
val feat = FeatureId::ReplayStart
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("ReplayStart")
```

</details>

#### ReplayStop round-trips through i32

- ReplayStop round-trips through i32
   - Expected: back.to_string() equals `ReplayStop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ReplayStop round-trips through i32")
val feat = FeatureId::ReplayStop
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("ReplayStop")
```

</details>

#### ReverseFinish round-trips through i32

- ReverseFinish round-trips through i32
   - Expected: back.to_string() equals `ReverseFinish`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ReverseFinish round-trips through i32")
val feat = FeatureId::ReverseFinish
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("ReverseFinish")
```

</details>

#### ReverseWatch round-trips through i32

- ReverseWatch round-trips through i32
   - Expected: back.to_string() equals `ReverseWatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ReverseWatch round-trips through i32")
val feat = FeatureId::ReverseWatch
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("ReverseWatch")
```

</details>

#### CheckpointSave round-trips through i32

- CheckpointSave round-trips through i32
   - Expected: back.to_string() equals `CheckpointSave`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CheckpointSave round-trips through i32")
val feat = FeatureId::CheckpointSave
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("CheckpointSave")
```

</details>

#### CheckpointRestore round-trips through i32

- CheckpointRestore round-trips through i32
   - Expected: back.to_string() equals `CheckpointRestore`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CheckpointRestore round-trips through i32")
val feat = FeatureId::CheckpointRestore
val id = feat.to_i32()
val back = FeatureId.from_i32(id)
expect(back.to_string()).to_equal("CheckpointRestore")
```

</details>

### Replay FeatureId to_text

#### RecordStart to_text returns correct string

- RecordStart to_text returns correct string
   - Expected: FeatureId::RecordStart.to_text() equals `RecordStart`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("RecordStart to_text returns correct string")
expect(FeatureId::RecordStart.to_text()).to_equal("RecordStart")
```

</details>

#### CheckpointRestore to_text returns correct string

- CheckpointRestore to_text returns correct string
   - Expected: FeatureId::CheckpointRestore.to_text() equals `CheckpointRestore`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CheckpointRestore to_text returns correct string")
expect(FeatureId::CheckpointRestore.to_text()).to_equal("CheckpointRestore")
```

</details>

### Replay FeatureId edge cases

#### from_i32 with invalid ID returns default (Halt)

- from_i32 with invalid ID returns default (Halt)
   - Expected: feat.to_string() equals `Halt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("from_i32 with invalid ID returns default (Halt)")
val feat = FeatureId.from_i32(9999)
expect(feat.to_string()).to_equal("Halt")
```

</details>

#### all 8 replay variants have distinct IDs

- all 8 replay variants have distinct IDs
   - Expected: all_distinct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all 8 replay variants have distinct IDs")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Replay FeatureId round-trip (to_i32 -> from_i32), Replay FeatureId to_text, Replay FeatureId edge cases.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5ebb20b99ac9dfe4dcd7f13a8c571d10240a9671965254e6e61d01aefa4e68a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ebb20b99ac9dfe4dcd7f13a8c571d10240a9671965254e6e61d01aefa4e68a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ebb20b99ac9dfe4dcd7f13a8c571d10240a9671965254e6e61d01aefa4e68a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/replay_feature_registry_spec.spl
mirror: doc/06_spec/03_system/tools/replay_feature_registry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/replay_feature_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/replay_feature_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/replay_feature_registry_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RecordStart round-trips through i32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_feature_registry_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RecordStop round-trips through i32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_feature_registry_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ReplayStart round-trips through i32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
