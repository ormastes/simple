# Md Diagram Update Block Specification

> <details>

<!-- sdn-diagram:id=md_diagram_update_block_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_diagram_update_block_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_diagram_update_block_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_diagram_update_block_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Diagram Update Block Specification

## Scenarios

### md-diagram-update block emitter

#### preserves safe diagram ids in generated markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = emit_diagram_block("doc.arch", "A: A", "sha256:auto", "+---+")
expect(block).to_contain("<!-- sdn-diagram:id=doc.arch -->")
expect(block).to_contain("```sdn id=doc.arch hash=sha256:auto render=ascii")
expect(block).to_contain("```ascii generated-from=doc.arch hash=sha256:auto")
```

</details>

#### falls back for unsafe diagram ids in generated markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = emit_diagram_block("doc arch`bad", "A: A", "sha256:auto", "+---+")
expect(block).to_contain("<!-- sdn-diagram:id=diagram -->")
expect(block).to_contain("```sdn id=diagram hash=sha256:auto render=ascii")
expect(block).to_contain("```ascii generated-from=diagram hash=sha256:auto")
expect(block.contains("doc arch`bad")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/md_diagram_update_block_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- md-diagram-update block emitter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
