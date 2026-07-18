# Tauri App Policy Specification

> <details>

<!-- sdn-diagram:id=tauri_app_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_app_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_app_policy_spec -> std
tauri_app_policy_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_app_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri App Policy Specification

## Scenarios

### Tauri app policy

#### detects shared WM requests from CLI or env

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tauri_shared_wm_requested([], "")).to_equal(false)
expect(tauri_shared_wm_requested([], "0")).to_equal(false)
expect(tauri_shared_wm_requested([], "1")).to_equal(true)
expect(tauri_shared_wm_requested(["--shared-wm"], "")).to_equal(true)
```

</details>

#### documents the standalone shared WM limitation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = tauri_shared_wm_error()
expect(error).to_contain("shared WM mode is not supported")
expect(error).to_contain("browser or electron")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/tauri_app_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tauri app policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
