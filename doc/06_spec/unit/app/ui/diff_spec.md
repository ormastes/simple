# Diff Specification

> Tests covering diff, diff children, DiffResult, ChildSnapshot, snapshot_children.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diff Specification

## Scenarios

### diff

#### returns empty patches for identical trees

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns empty patches for identical trees


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty patches for identical trees")
expect true  # diff(elem, elem.clone()) -> empty patches
```

</details>

#### detects text changes

- detects text changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects text changes")
expect true  # old "Hello" vs new "World" -> SetText patch
```

</details>

#### detects attribute additions

- detects attribute additions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects attribute additions")
expect true  # old no attr vs new with_attr -> SetAttr patch
```

</details>

#### detects attribute removals

- detects attribute removals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects attribute removals")
expect true  # old with_attr vs new no attr -> RemoveAttr patch
```

</details>

#### detects attribute changes

- detects attribute changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects attribute changes")
expect true  # old attr="a" vs new attr="b" -> SetAttr patch
```

</details>

#### detects class additions

- detects class additions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects class additions")
expect true  # old no class vs new with_class -> AddClass patch
```

</details>

#### detects class removals

- detects class removals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects class removals")
expect true  # old with_class vs new no class -> RemoveClass patch
```

</details>

#### detects focus changes

- detects focus changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects focus changes")
expect true  # old unfocused vs new focused -> SetFocus patch
```

</details>

### diff children

#### handles empty children

- handles empty children


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty children")
expect true  # both empty -> no patches
```

</details>

#### detects new children

- detects new children


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects new children")
expect true  # old empty vs new with child -> InsertChild patch
```

</details>

#### detects removed children

- detects removed children


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects removed children")
expect true  # old with child vs new empty -> RemoveChild patch
```

</details>

#### matches keyed children

- matches keyed children


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches keyed children")
expect true  # keyed reordering -> MoveChild patches
```

</details>

#### handles child updates

- handles child updates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles child updates")
expect true  # child text changed -> SetText patch
```

</details>

### DiffResult

#### provides patches accessor

- provides patches accessor


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides patches accessor")
expect true  # result.patches()
```

</details>

#### allows taking patches

- allows taking patches


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows taking patches")
expect true  # result.take_patches()
```

</details>

### ChildSnapshot

#### creates snapshot from element

- creates snapshot from element


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates snapshot from element")
expect true  # ChildSnapshot.from_element(&elem)
```

</details>

#### creates snapshot without key

- creates snapshot without key


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates snapshot without key")
expect true  # elem without key -> snapshot.key.is_none()
```

</details>

### snapshot_children

#### creates snapshots from children array

- creates snapshots from children array


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates snapshots from children array")
expect true  # snapshot_children(&[a, b, c])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/diff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering diff, diff children, DiffResult, ChildSnapshot, snapshot_children.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `edb066c72526ea57d983650cd5a6e974b3ef1660d6f5dadc5c904e0eba790463`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `edb066c72526ea57d983650cd5a6e974b3ef1660d6f5dadc5c904e0eba790463`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `edb066c72526ea57d983650cd5a6e974b3ef1660d6f5dadc5c904e0eba790463`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/diff_spec.spl
mirror: doc/06_spec/unit/app/ui/diff_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/diff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/diff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/diff_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty patches for identical trees' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/diff_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects text changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/diff_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects attribute additions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
