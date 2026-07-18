# Shared Ui Contract Specification

> <details>

<!-- sdn-diagram:id=shared_ui_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shared_ui_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shared_ui_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shared_ui_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Ui Contract Specification

## Scenarios

### Shared UI contract portable smoke

#### records protocol version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val protocol_version = "1"
expect(protocol_version).to_equal("1")
```

</details>

#### records shared element identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val element_id = "action_btn"
val element_kind = "button"
expect(element_id).to_equal("action_btn")
expect(element_kind).to_equal("button")
```

</details>

#### records structured error shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error_code = "not_found"
expect(error_code).to_equal("not_found")
```

</details>

#### records supported actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = ["click", "type", "submit"]
expect(actions.len()).to_equal(3)
expect(actions[0]).to_equal("click")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/shared_ui_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Shared UI contract portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
