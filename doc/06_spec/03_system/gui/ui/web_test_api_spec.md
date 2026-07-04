# Web Test Api Specification

> <details>

<!-- sdn-diagram:id=web_test_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_test_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_test_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_test_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Test Api Specification

## Scenarios

### Web UI Test API portable smoke

#### records ready and state endpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("/api/test/ready").to_equal("/api/test/ready")
expect("NORMAL").to_equal("NORMAL")
```

</details>

#### records element query contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("action_btn").to_equal("action_btn")
expect("button").to_equal("button")
```

</details>

#### records supported actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val actions = ["click", "type", "key"]
expect(actions.len()).to_equal(3)
expect(actions[0]).to_equal("click")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/ui/web_test_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Web UI Test API portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
