# Tauri Entry Common Envelope Specification

> 1. Ok

<!-- sdn-diagram:id=tauri_entry_common_envelope_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_entry_common_envelope_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_entry_common_envelope_spec -> std
tauri_entry_common_envelope_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_entry_common_envelope_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri Entry Common Envelope Specification

## Scenarios

### Tauri static render entry common envelope

#### emits common WebRender metadata for one-shot .ui.sdn render exports

1. Ok
2. Err
   - Expected: "tauri_entry_render_ipc failed: {e}" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tauri_entry_render_ipc("examples/06_io/ui/hello_tauri.ui.sdn")
match result:
    Ok(json):
        expect(json).to_contain("\"type\":\"render\"")
        expect(json).to_contain("\"target\":\"tauri\"")
        expect(json).to_contain("\"surface_id\":\"main\"")
        expect(json).to_contain("\"width\":1280")
        expect(json).to_contain("\"height\":720")
        expect(json).to_contain("Hello Tauri")
    Err(e):
        expect("tauri_entry_render_ipc failed: {e}").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/tauri_entry_common_envelope_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tauri static render entry common envelope

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
