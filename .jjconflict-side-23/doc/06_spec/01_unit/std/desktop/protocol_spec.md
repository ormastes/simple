# Protocol Specification

> <details>

<!-- sdn-diagram:id=protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

protocol_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protocol Specification

## Scenarios

### Desktop Protocol Handler API

#### creates ProtocolConfig struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ProtocolConfig(scheme: "myapp", app_name: "My App", binary_path: "/usr/bin/myapp")
expect config.scheme == "myapp"
expect config.app_name == "My App"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/protocol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desktop Protocol Handler API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
