# Dom Accessors Specification

> <details>

<!-- sdn-diagram:id=dom_accessors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dom_accessors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dom_accessors_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dom_accessors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dom Accessors Specification

## Scenarios

### browser DOM accessors

#### concatenates descendant text in source order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text_content = be_dom_get_text_content(_accessor_tree())

expect(text_content).to_equal("alphabeta")
```

</details>

#### finds descendants by id and tag through recursive scans

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _accessor_tree()
val found = be_dom_find_by_id(root, 5)
val sections = be_dom_find_by_tag(root, "section")

expect(found == nil).to_be(false)
expect(found.unwrap().tag_name).to_equal("span")
expect(sections.len()).to_equal(2)
expect(sections[0].node_id).to_equal(2)
expect(sections[1].node_id).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_accessors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- browser DOM accessors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
