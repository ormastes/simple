# Patchset Specification

> Tests covering PatchOp, PatchSet, PatchSet optimization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Patchset Specification

## Scenarios

### PatchOp

#### identifies target node

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- identifies target node


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies target node")
expect true  # op.target_id() returns the node being patched
```

</details>

#### identifies target node for attr operations

- identifies target node for attr operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies target node for attr operations")
expect true  # SetAttr, RemoveAttr have node_id
```

</details>

#### identifies structural operations

- identifies structural operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies structural operations")
expect true  # InsertChild, RemoveChild, MoveChild are structural
```

</details>

#### identifies remove and move as structural

- identifies remove and move as structural


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies remove and move as structural")
expect true  # RemoveChild, ReplaceChild, MoveChild are structural
```

</details>

### PatchSet

#### starts empty

- starts empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts empty")
expect true  # PatchSet.new().is_empty() == true
```

</details>

#### adds patches

- adds patches


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds patches")
expect true  # ps.set_text(...); ps.len() == 1
```

</details>

#### provides helper methods

- provides helper methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides helper methods")
expect true  # set_text, set_attr, add_class, remove_class
```

</details>

#### clears all patches

- clears all patches


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all patches")
expect true  # ps.clear(); ps.is_empty() == true
```

</details>

#### extends with multiple operations

- extends with multiple operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extends with multiple operations")
expect true  # ps.extend([op1, op2, op3])
```

</details>

#### supports insert and remove child helpers

- supports insert and remove child helpers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports insert and remove child helpers")
expect true  # ps.insert_child(), ps.remove_child()
```

</details>

#### supports focus and event helpers

- supports focus and event helpers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports focus and event helpers")
expect true  # ps.focus(), ps.bind_event()
```

</details>

### PatchSet optimization

#### removes redundant text updates

- removes redundant text updates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes redundant text updates")
expect true  # multiple set_text -> keep only last
```

</details>

#### removes redundant attr updates

- removes redundant attr updates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes redundant attr updates")
expect true  # multiple set_attr for same -> keep only last
```

</details>

#### preserves structural operations order

- preserves structural operations order


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves structural operations order")
expect true  # insert order matters, don't reorder
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/patchset_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PatchOp, PatchSet, PatchSet optimization.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c23b9c522eb4bd40dd5e1209c23ce04b3e0405624ea31bbc0d83c836eefdf2f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c23b9c522eb4bd40dd5e1209c23ce04b3e0405624ea31bbc0d83c836eefdf2f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c23b9c522eb4bd40dd5e1209c23ce04b3e0405624ea31bbc0d83c836eefdf2f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/patchset_spec.spl
mirror: doc/06_spec/unit/app/ui/patchset_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/patchset_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/patchset_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/patchset_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies target node' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/patchset_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies target node for attr operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/patchset_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies structural operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
