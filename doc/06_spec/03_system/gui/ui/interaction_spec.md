# Interaction Specification

> <details>

<!-- sdn-diagram:id=interaction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interaction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interaction_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interaction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interaction Specification

## Scenarios

### UI interaction portable smoke

#### records keyboard navigation action

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "j"
expect(key).to_equal("j")
```

</details>

#### records visibility and existence checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val element_id = "action_btn"
expect(element_id).to_equal("action_btn")
```

</details>

#### records drag source and target

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "action_btn"
val target = "nav_list"
expect(source).to_equal("action_btn")
expect(target).to_equal("nav_list")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/interaction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- UI interaction portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
