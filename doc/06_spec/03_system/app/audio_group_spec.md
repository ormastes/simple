# Audio Group Specification

> Tests covering AudioGroupTree — empty tree, AudioGroupTree — add groups, AudioGroupTree — effective volume, AudioGroupTree — effective muted, AudioGroupTree — set volume.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audio Group Specification

## Scenarios

### AudioGroupTree — empty tree

#### new tree has no groups

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- new tree has no groups


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("new tree has no groups")
val tree = AudioGroupTree.new()
val g = tree.get_group("anything")
expect(g).to_be_nil()
```

</details>

### AudioGroupTree — add groups

#### add root group makes it retrievable

- add root group makes it retrievable
   - Expected: g.name equals `master`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("add root group makes it retrievable")
var tree = AudioGroupTree.new()
tree.add_group("master", "")
val g = tree.get_group("master")
expect(g.name).to_equal("master")
```

</details>

#### add child group with correct parent

- add child group with correct parent
   - Expected: g.name equals `sfx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("add child group with correct parent")
var tree = AudioGroupTree.new()
tree.add_group("master", "")
tree.add_group("sfx", "master")
val g = tree.get_group("sfx")
expect(g.name).to_equal("sfx")
```

</details>

### AudioGroupTree — effective volume

#### parent 0.5 times child 0.8 equals 0.4

- parent 0.5 times child 0.8 equals 0.4
   - Expected: vol.value > 0.39 is true
   - Expected: vol.value < 0.41 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parent 0.5 times child 0.8 equals 0.4")
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

- mute parent makes child effectively muted
   - Expected: muted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mute parent makes child effectively muted")
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

- set_volume updates group volume
   - Expected: vol.value > 0.69 is true
   - Expected: vol.value < 0.71 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("set_volume updates group volume")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AudioGroupTree — empty tree, AudioGroupTree — add groups, AudioGroupTree — effective volume, AudioGroupTree — effective muted, AudioGroupTree — set volume.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e8586c4f6950fd06fcf429f492445782664ca443dbad2a1961c3a8df13c65cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e8586c4f6950fd06fcf429f492445782664ca443dbad2a1961c3a8df13c65cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e8586c4f6950fd06fcf429f492445782664ca443dbad2a1961c3a8df13c65cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/audio_group_spec.spl
mirror: doc/06_spec/03_system/app/audio_group_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/audio_group_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/audio_group_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/audio_group_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new tree has no groups' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/audio_group_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add root group makes it retrievable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/audio_group_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add child group with correct parent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
