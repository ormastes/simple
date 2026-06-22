# Wire Golden Specification

> <details>

<!-- sdn-diagram:id=wire_golden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wire_golden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wire_golden_spec -> std
wire_golden_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wire_golden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wire Golden Specification

## Scenarios

### UI wire-protocol golden bytes

#### encodes empty snapshot byte-identically

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = ui_access_snapshot_to_json(_empty_snapshot())
expect(out).to_equal(GOLDEN_EMPTY)
```

</details>

#### encodes single-panel snapshot byte-identically

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = ui_access_snapshot_to_json(_single_panel_snapshot())
expect(out).to_equal(GOLDEN_SINGLE_PANEL)
```

</details>

#### encodes multi-widget snapshot byte-identically

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = ui_access_snapshot_to_json(_multi_widget_snapshot())
expect(out).to_equal(GOLDEN_MULTI_WIDGET)
```

</details>

#### freezes UI_ACCESS_PROTOCOL_VERSION at v1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(UI_ACCESS_PROTOCOL_VERSION).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/wire_golden/wire_golden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- UI wire-protocol golden bytes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
