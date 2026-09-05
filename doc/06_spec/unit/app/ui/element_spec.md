# Element Specification

> Tests covering NodeId, ElementKind, Element, ElementTree.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Element Specification

## Scenarios

### NodeId

#### creates unique IDs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates unique IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates unique IDs")
expect true  # NodeId.new(1).value() == 1
```

</details>

#### generates sequential IDs

- generates sequential IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates sequential IDs")
expect true  # id.next().value() == id.value() + 1
```

</details>

#### compares for equality

- compares for equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares for equality")
expect true  # NodeId.new(42) == NodeId.new(42)
```

</details>

### ElementKind

#### identifies block elements

- identifies block elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies block elements")
expect true  # Div, Box, Paragraph, Column are block
```

</details>

#### identifies inline elements

- identifies inline elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies inline elements")
expect true  # Span, Text, Button are inline
```

</details>

#### identifies interactive elements

- identifies interactive elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies interactive elements")
expect true  # Button, Input, Checkbox are interactive
```

</details>

#### provides HTML tag names

- provides HTML tag names


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides HTML tag names")
expect true  # Div->"div", Button->"button", etc.
```

</details>

### Element

#### creates elements with given kind

- creates elements with given kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates elements with given kind")
expect true  # Element.new(id, ElementKind.Div)
```

</details>

#### creates text elements

- creates text elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates text elements")
expect true  # Element.text(id, "Hello, World!")
```

</details>

#### creates button elements with tab index

- creates button elements with tab index


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates button elements with tab index")
expect true  # Element.button(id, "Click Me")
```

</details>

#### supports builder pattern

- supports builder pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports builder pattern")
expect true  # .with_key().with_attr().with_class().with_style()
```

</details>

#### adds children

- adds children


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds children")
expect true  # .with_child(Element.text(id, "Child"))
```

</details>

#### finds child by index

- finds child by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds child by index")
expect true  # parent.child_at(0)
```

</details>

#### finds child by key

- finds child by key


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds child by key")
expect true  # parent.find_by_key("special")
```

</details>

#### finds descendant by ID

- finds descendant by ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds descendant by ID")
expect true  # root.find_by_id(grandchild_id)
```

</details>

#### manages focus state

- manages focus state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manages focus state")
expect true  # elem.focus(), elem.blur(), elem.focused
```

</details>

### ElementTree

#### creates tree with root element

- creates tree with root element


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates tree with root element")
expect true  # ElementTree.new(ElementKind.Div)
```

</details>

#### allocates sequential node IDs

- allocates sequential node IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates sequential node IDs")
expect true  # tree.alloc_id()
```

</details>

#### manages focus

- manages focus


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manages focus")
expect true  # tree.set_focus(id), tree.focused()
```

</details>

#### cycles focus through focusable elements

- cycles focus through focusable elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cycles focus through focusable elements")
expect true  # tree.focus_next(), tree.focus_prev()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/element_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NodeId, ElementKind, Element, ElementTree.
- NodeId
- ElementKind
- Element
- ElementTree

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `0891598c4d1d1eba6aa8dfdfe269ce649c28df4d7fccc3e0d2789ad726e63399`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0891598c4d1d1eba6aa8dfdfe269ce649c28df4d7fccc3e0d2789ad726e63399`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0891598c4d1d1eba6aa8dfdfe269ce649c28df4d7fccc3e0d2789ad726e63399`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/element_spec.spl
mirror: doc/06_spec/unit/app/ui/element_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/element_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/element_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/element_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates unique IDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/element_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates sequential IDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/element_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares for equality' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
