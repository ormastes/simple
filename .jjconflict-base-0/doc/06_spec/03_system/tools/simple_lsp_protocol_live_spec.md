# Simple Lsp Protocol Live Specification

> <details>

<!-- sdn-diagram:id=simple_lsp_protocol_live_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_lsp_protocol_live_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_lsp_protocol_live_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_lsp_protocol_live_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Lsp Protocol Live Specification

## Scenarios

### Simple LSP live protocol smoke

#### responds to initialize, didOpen, completion, definition, codeAction, and shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run("bin/simple", ["run", "scripts/smoke/simple_lsp_protocol_smoke.spl"])
expect(result.2).to_equal(0)
expect(result.0).to_contain("STATUS: PASS simple_lsp_protocol_smoke")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/simple_lsp_protocol_live_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple LSP live protocol smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
