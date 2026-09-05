# DOM Query Specification

> Tests for `be_dom_find_by_id` and `be_dom_query_selector` tree-walk helpers added to `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` (REQ-3 / AC-2). All specs FAIL until those functions are implemented.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DOM Query Specification

Tests for `be_dom_find_by_id` and `be_dom_query_selector` tree-walk helpers added to `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` (REQ-3 / AC-2). All specs FAIL until those functions are implemented.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M15-DOM-QUERY |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/browser_engine/script/dom_query_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for `be_dom_find_by_id` and `be_dom_query_selector` tree-walk helpers
added to `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` (REQ-3 / AC-2).
All specs FAIL until those functions are implemented.

## Key Behaviors

- `be_dom_find_by_id` walks the `BeDomNode` tree recursively and returns the
  first node whose `id` field equals the target, or nil if not found.
- `be_dom_query_selector` supports simple selectors: tag name, `#id`, `.class`.
  Returns first matching node or nil.

## Scenarios

### be_dom_find_by_id

### AC-2: getElementById — flat tree

#### AC-2: finds the root node when id matches root

- AC-2: finds the root node when id matches root
   - Expected: found equals `root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: finds the root node when id matches root")
val root = _make_leaf("div", "main")
val found = be_dom_find_by_id(root, "main")
expect(found).to_equal(root)
```

</details>

#### AC-2: finds a direct child by id

- AC-2: finds a direct child by id
   - Expected: found.id equals `child1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: finds a direct child by id")
val root = _make_root_with_two_children()
val found = be_dom_find_by_id(root, "child1")
expect(found.id).to_equal("child1")
```

</details>

#### AC-2: finds second child by id

- AC-2: finds second child by id
   - Expected: found.id equals `child2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: finds second child by id")
val root = _make_root_with_two_children()
val found = be_dom_find_by_id(root, "child2")
expect(found.id).to_equal("child2")
```

</details>

#### AC-2: returns nil when id not present in flat tree

- AC-2: returns nil when id not present in flat tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: returns nil when id not present in flat tree")
val root = _make_root_with_two_children()
val found = be_dom_find_by_id(root, "nonexistent")
expect(found).to_be_nil()
```

</details>

### AC-2: getElementById — deep tree

#### AC-2: finds a deeply nested node by id

- AC-2: finds a deeply nested node by id
   - Expected: found.id equals `deep-button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: finds a deeply nested node by id")
val root = _make_deep_tree()
val found = be_dom_find_by_id(root, "deep-button")
expect(found.id).to_equal("deep-button")
```

</details>

#### AC-2: finds intermediate node by id

- AC-2: finds intermediate node by id
   - Expected: found.id equals `mid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: finds intermediate node by id")
val root = _make_deep_tree()
val found = be_dom_find_by_id(root, "mid")
expect(found.id).to_equal("mid")
```

</details>

#### AC-2: returns nil for id absent from deep tree

- AC-2: returns nil for id absent from deep tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: returns nil for id absent from deep tree")
val root = _make_deep_tree()
val found = be_dom_find_by_id(root, "ghost")
expect(found).to_be_nil()
```

</details>

### AC-2: getElementById — empty tree

#### AC-2: returns nil on a childless node with non-matching id

- AC-2: returns nil on a childless node with non-matching id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: returns nil on a childless node with non-matching id")
val root = _make_leaf("div", "only")
val found = be_dom_find_by_id(root, "other")
expect(found).to_be_nil()
```

</details>

### be_dom_query_selector

### AC-2: querySelector by tag

#### AC-2: matches root node by its own tag name

- AC-2: matches root node by its own tag name
   - Expected: found.tag equals `section`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: matches root node by its own tag name")
val root = _make_leaf("section", "")
val found = be_dom_query_selector(root, "section")
expect(found.tag).to_equal("section")
```

</details>

#### AC-2: matches first child tag when root tag does not match

- AC-2: matches first child tag when root tag does not match
   - Expected: found.tag equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: matches first child tag when root tag does not match")
val root = _make_multi_tag_tree()
val found = be_dom_query_selector(root, "p")
expect(found.tag).to_equal("p")
```

</details>

#### AC-2: matches second child tag

- AC-2: matches second child tag
   - Expected: found.tag equals `h1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: matches second child tag")
val root = _make_multi_tag_tree()
val found = be_dom_query_selector(root, "h1")
expect(found.tag).to_equal("h1")
```

</details>

#### AC-2: returns nil when no tag matches

- AC-2: returns nil when no tag matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: returns nil when no tag matches")
val root = _make_multi_tag_tree()
val found = be_dom_query_selector(root, "table")
expect(found).to_be_nil()
```

</details>

### AC-2: querySelector by id selector

#### AC-2: #id selector finds node by id field

- AC-2: #id selector finds node by id field
   - Expected: found.id equals `child2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: #id selector finds node by id field")
val root = _make_root_with_two_children()
val found = be_dom_query_selector(root, "#child2")
expect(found.id).to_equal("child2")
```

</details>

#### AC-2: #id selector returns nil when id absent

- AC-2: #id selector returns nil when id absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: #id selector returns nil when id absent")
val root = _make_root_with_two_children()
val found = be_dom_query_selector(root, "#missing")
expect(found).to_be_nil()
```

</details>

### AC-2: querySelector by class selector

#### AC-2: .class selector finds node that has the class

- AC-2: .class selector finds node that has the class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: .class selector finds node that has the class")
val root = _make_classed_tree()
val found = be_dom_query_selector(root, ".highlight")
expect(found.classes).to_contain("highlight")
```

</details>

#### AC-2: .class selector returns nil when no node has the class

- AC-2: .class selector returns nil when no node has the class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: .class selector returns nil when no node has the class")
val root = _make_classed_tree()
val found = be_dom_query_selector(root, ".absent")
expect(found).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `96bd3b10021dd6abe98e05cb8c46d7892a06942aac3f9c5e954045750878e508`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96bd3b10021dd6abe98e05cb8c46d7892a06942aac3f9c5e954045750878e508`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96bd3b10021dd6abe98e05cb8c46d7892a06942aac3f9c5e954045750878e508`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/browser_engine/script/dom_query_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/script/dom_query_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/script/dom_query_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/script/dom_query_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/script/dom_query_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: finds the root node when id matches root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/script/dom_query_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: finds a direct child by id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/script/dom_query_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: finds second child by id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
