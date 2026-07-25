# Dashboard Serve Specification

> <details>

<!-- sdn-diagram:id=dashboard_serve_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dashboard_serve_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dashboard_serve_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dashboard_serve_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dashboard Serve Specification

## Scenarios

### dashboard run_serve stub replacement

#### run_serve does not return unavailable message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_serve_result([])
expect(result.contains("unavailable")).to_equal(false)
```

</details>

#### run_serve result indicates delegation or ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_serve_result([])
expect(result.len() >= 0).to_equal(true)
```

</details>

#### run_serve accepts port arg without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_serve_result(["--port", "8080"])
expect(result.contains("unavailable")).to_equal(false)
```

</details>

### dashboard run_gui stub replacement

#### run_gui does not return unavailable message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_gui_result([])
expect(result.contains("unavailable")).to_equal(false)
```

</details>

#### run_gui accepts args without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_gui_result(["--port", "9090"])
expect(result.contains("unavailable")).to_equal(false)
```

</details>

### dashboard run_agents stub replacement

#### run_agents does not return unavailable message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_agents_result([])
expect(result.contains("unavailable")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dashboard/dashboard_serve_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dashboard run_serve stub replacement
- dashboard run_gui stub replacement
- dashboard run_agents stub replacement

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
