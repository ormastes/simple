# Shell Open Specification

> <details>

<!-- sdn-diagram:id=shell_open_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_open_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_open_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_open_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Open Specification

## Scenarios

### Desktop Shell Integration

#### exposes open_url function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell_open_source()).to_contain("fn open_url(url: text)")
```

</details>

#### exposes show_in_folder function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell_open_source()).to_contain("fn show_in_folder(path: text)")
```

</details>

#### exposes move_to_trash function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell_open_source()).to_contain("fn move_to_trash(path: text)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/shell_open_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desktop Shell Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
