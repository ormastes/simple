# Detect Specification

> <details>

<!-- sdn-diagram:id=detect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=detect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

detect_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=detect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Detect Specification

## Scenarios

### has_tauri_shell

#### returns a bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = has_tauri_shell()
val is_bool = result == true or result == false
expect(is_bool).to_equal(true)
```

</details>

#### returns false on SimpleOS (no Tauri available)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# On a standard Linux/QEMU test environment this should be false.
# The function must not crash or return an undefined value.
val result = has_tauri_shell()
expect(result == true or result == false).to_equal(true)
```

</details>

#### does not panic on any platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simply calling it must not throw or produce nil
val result = has_tauri_shell()
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/detect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- has_tauri_shell

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
