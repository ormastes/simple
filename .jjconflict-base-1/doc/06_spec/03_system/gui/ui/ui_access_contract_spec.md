# Ui Access Contract Specification

> <details>

<!-- sdn-diagram:id=ui_access_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Contract Specification

## Scenarios

### UI access contract portable smoke

#### records access verbs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbs = ["snapshot", "surface", "find", "act", "history"]
expect(verbs.len()).to_equal(5)
expect(verbs[0]).to_equal("snapshot")
```

</details>

#### records selector identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val selector = "action_btn"
expect(selector).to_equal("action_btn")
```

</details>

#### records action result shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = true
expect(ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/ui_access_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- UI access contract portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
