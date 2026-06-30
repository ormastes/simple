# Ios Mode Specification

> <details>

<!-- sdn-diagram:id=ios_mode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ios_mode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ios_mode_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ios_mode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ios Mode Specification

## Scenarios

### ios_mode

### DashboardServer.new_ios

#### AC-3: new_ios constructor sets is_ios to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_ios(3099, "")
expect(server.is_ios).to_equal(true)
```

</details>

#### AC-3: new_ios constructor records the port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_ios(3099, "")
expect(server.port).to_equal(3099)
```

</details>

#### AC-3: new (non-iOS) constructor keeps is_ios false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new(3099)
expect(server.is_ios).to_equal(false)
```

</details>

#### AC-3: new_with_agent_dir constructor keeps is_ios false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_agent_dir(3099, "/tmp/agents")
expect(server.is_ios).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/ios_mode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ios_mode
- DashboardServer.new_ios

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
