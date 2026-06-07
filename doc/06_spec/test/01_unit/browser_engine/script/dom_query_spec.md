# DOM Query Specification

> Tests for `be_dom_find_by_id` and `be_dom_query_selector` tree-walk helpers added to `src/lib/gc_async_mut/gpu/browser_engine/dom.spl` (REQ-3 / AC-2). All specs FAIL until those functions are implemented.

<!-- sdn-diagram:id=dom_query_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dom_query_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dom_query_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dom_query_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_leaf("div", "main")
val found = be_dom_find_by_id(root, "main")
expect(found).to_equal(root)
```

</details>

#### AC-2: finds a direct child by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_root_with_two_children()
val found = be_dom_find_by_id(root, "child1")
expect(found.id).to_equal("child1")
```

</details>

#### AC-2: finds second child by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_root_with_two_children()
val found = be_dom_find_by_id(root, "child2")
expect(found.id).to_equal("child2")
```

</details>

#### AC-2: returns nil when id not present in flat tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_root_with_two_children()
val found = be_dom_find_by_id(root, "nonexistent")
expect(found).to_be_nil()
```

</details>

### AC-2: getElementById — deep tree

#### AC-2: finds a deeply nested node by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_deep_tree()
val found = be_dom_find_by_id(root, "deep-button")
expect(found.id).to_equal("deep-button")
```

</details>

#### AC-2: finds intermediate node by id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_deep_tree()
val found = be_dom_find_by_id(root, "mid")
expect(found.id).to_equal("mid")
```

</details>

#### AC-2: returns nil for id absent from deep tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_deep_tree()
val found = be_dom_find_by_id(root, "ghost")
expect(found).to_be_nil()
```

</details>

### AC-2: getElementById — empty tree

#### AC-2: returns nil on a childless node with non-matching id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_leaf("div", "only")
val found = be_dom_find_by_id(root, "other")
expect(found).to_be_nil()
```

</details>

### be_dom_query_selector

### AC-2: querySelector by tag

#### AC-2: matches root node by its own tag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_leaf("section", "")
val found = be_dom_query_selector(root, "section")
expect(found.tag).to_equal("section")
```

</details>

#### AC-2: matches first child tag when root tag does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_multi_tag_tree()
val found = be_dom_query_selector(root, "p")
expect(found.tag).to_equal("p")
```

</details>

#### AC-2: matches second child tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_multi_tag_tree()
val found = be_dom_query_selector(root, "h1")
expect(found.tag).to_equal("h1")
```

</details>

#### AC-2: returns nil when no tag matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_multi_tag_tree()
val found = be_dom_query_selector(root, "table")
expect(found).to_be_nil()
```

</details>

### AC-2: querySelector by id selector

#### AC-2: #id selector finds node by id field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_root_with_two_children()
val found = be_dom_query_selector(root, "#child2")
expect(found.id).to_equal("child2")
```

</details>

#### AC-2: #id selector returns nil when id absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_root_with_two_children()
val found = be_dom_query_selector(root, "#missing")
expect(found).to_be_nil()
```

</details>

### AC-2: querySelector by class selector

#### AC-2: .class selector finds node that has the class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _make_classed_tree()
val found = be_dom_query_selector(root, ".highlight")
expect(found.classes).to_contain("highlight")
```

</details>

#### AC-2: .class selector returns nil when no node has the class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
