# Context Pack Specification

> <details>

<!-- sdn-diagram:id=context_pack_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_pack_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_pack_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_pack_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Pack Specification

## Scenarios

### Context Pack

#### keeps context packer model and constructor available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_sync_mut/engine/llm/context_packer.spl") ?? ""

expect(source).to_contain("struct ContextEntry")
expect(source).to_contain("class ContextPacker")
expect(source).to_contain("static fn new(max_entries: i64) -> ContextPacker")
```

</details>

#### keeps context packer entry mutation helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_sync_mut/engine/llm/context_packer.spl") ?? ""

expect(source).to_contain("me add_entry(category: text, key: text, value: text)")
expect(source).to_contain("me add_scene_info(scene_name: text, node_count: i64)")
expect(source).to_contain("me add_physics_info(body_count: i64, gravity: f64)")
expect(source).to_contain("me clear()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/context_pack_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Context Pack

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
