# Anonymous Block Specification

> <details>

<!-- sdn-diagram:id=anonymous_block_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=anonymous_block_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

anonymous_block_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=anonymous_block_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Anonymous Block Specification

## Scenarios

### Anonymous block generation

#### AC-3: wraps leading inline text before block sibling in anon block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _build_and_layout("<div>text<p>block</p></div>")
val anon_count = _count_anon_blocks(box_)
expect(anon_count).to_be_greater_than(0)
```

</details>

#### AC-3: wraps trailing inline text after block sibling in anon block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _build_and_layout("<div><p>block</p>text after</div>")
val anon_count = _count_anon_blocks(box_)
expect(anon_count).to_be_greater_than(0)
```

</details>

#### AC-3: mixed inline and block children produce at least two layout children

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _build_and_layout("<div>before<p>block</p>after</div>")
val count = _child_box_count(box_)
expect(count).to_be_greater_than(1)
```

</details>

#### AC-3: block-only children produce zero anonymous blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box_ = _build_and_layout("<div><p>a</p><p>b</p></div>")
val anon_count = _count_anon_blocks(box_)
expect(anon_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/anonymous_block_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Anonymous block generation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
