# Clipboard Specification

> <details>

<!-- sdn-diagram:id=clipboard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=clipboard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

clipboard_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=clipboard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Clipboard Specification

## Scenarios

### Desktop Clipboard API

#### exposes clipboard_read function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clipboard_source()).to_contain("fn clipboard_read()")
```

</details>

#### exposes clipboard_write function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clipboard_source()).to_contain("fn clipboard_write(content: text)")
```

</details>

#### exposes clipboard_has_text function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clipboard_source()).to_contain("fn clipboard_has_text()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/clipboard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desktop Clipboard API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
