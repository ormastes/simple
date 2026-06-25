# Desktop E2e Shortcut Flow Specification

> <details>

<!-- sdn-diagram:id=desktop_e2e_shortcut_flow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=desktop_e2e_shortcut_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

desktop_e2e_shortcut_flow_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=desktop_e2e_shortcut_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Desktop E2e Shortcut Flow Specification

## Scenarios

### desktop e2e shortcut flow

#### does not return before SYS-GUI-002 shortcut and wm markers on no-vfs boots

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text(DESKTOP_E2E_ENTRY)
val skip_idx = source.find("[desktop-e2e] storage-backed-launch:skip reason=no-vfs")
val shortcut_idx = source.find("[desktop-e2e] shortcut dispatch begin")
val wm_idx = source.find("[desktop-e2e] wm:ok pid=")
val old_cutoff = "storage-backed-launch:skip reason=no-vfs\")\n        return true"

expect(skip_idx).to_be_greater_than(0)
expect(shortcut_idx).to_be_greater_than(skip_idx)
expect(wm_idx).to_be_greater_than(shortcut_idx)
expect(source.contains(old_cutoff)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/desktop_e2e_shortcut_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- desktop e2e shortcut flow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
