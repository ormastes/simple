# System Test - IDE Agent Dashboard SvLLM Integration

> End-to-end system test for IDE agent dashboard integration with svllm. Verifies that the dashboard consumes svllm readiness status and correctly maps engine state to dashboard lanes and integration gates.

<!-- sdn-diagram:id=ide_agent_dashboard_svllm_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_agent_dashboard_svllm_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_agent_dashboard_svllm_system_spec -> std
ide_agent_dashboard_svllm_system_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_agent_dashboard_svllm_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Test - IDE Agent Dashboard SvLLM Integration

End-to-end system test for IDE agent dashboard integration with svllm. Verifies that the dashboard consumes svllm readiness status and correctly maps engine state to dashboard lanes and integration gates.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #IDE-DASHBOARD-SVLLM |
| Category | IDE / ML Observability |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/03_system/tools/ide_agent_dashboard_svllm_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end system test for IDE agent dashboard integration with svllm.
Verifies that the dashboard consumes svllm readiness status and correctly
maps engine state to dashboard lanes and integration gates.

## Scenarios

### IDE Agent Dashboard SvLLM Integration

#### dashboard surface includes svllm-inference lane

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = ide_agent_dashboard_surface_svllm()
verify(surface.lanes.len() > 0)

var found_svllm_lane = false
for lane in surface.lanes:
    if lane.lane_id == "svllm-inference" and lane.provider == "svllm":
        found_svllm_lane = true

verify(found_svllm_lane)
```

</details>

#### offline svllm contributes zero blocking, degraded contributes one

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Real invariant: an offline svllm lane is non-blocking (mapped to
# "reviewed" inside the surface), exactly like a ready svllm — so it
# adds nothing to blocked_count. A DEGRADED svllm is the only state that
# blocks, and it must add exactly one.
val offline_surface = ide_agent_dashboard_surface_svllm_for(svllm_status_default())
val ready_surface = ide_agent_dashboard_surface_svllm_for(svllm_status_from(true, true, true, true, true, "demo-model"))
val degraded_surface = ide_agent_dashboard_surface_svllm_for(svllm_status_from(true, false, false, false, false, ""))

# offline and ready svllm contribute the SAME blocking (zero from svllm)
verify(offline_surface.blocked_count == ready_surface.blocked_count)
# degraded svllm adds exactly one blocked lane on top of that baseline
verify(degraded_surface.blocked_count == ready_surface.blocked_count + 1)
```

</details>

#### summary reflects live svllm readiness (not a hardcoded constant)

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Proves real status flow through the dashboard summary, both directions.
val ready_line = ide_agent_dashboard_summary_svllm_for(svllm_status_from(true, true, true, true, true, "demo-model"))
val offline_line = ide_agent_dashboard_summary_svllm_for(svllm_status_default())
verify(ready_line.ends_with("svllm=ready"))
verify(offline_line.ends_with("svllm=offline"))
```

</details>

#### svllm lane status maps ready status correctly

- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready_status = svllm_status_from(true, true, true, true, true, "demo-model")
val lane = ide_agent_dashboard_svllm_lane(ready_status)

verify(lane.lane_id == "svllm-inference")
verify(lane.provider == "svllm")
verify(lane.status == "ready")
```

</details>

#### svllm lane status maps degraded status correctly

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val degraded_status = svllm_status_from(true, false, false, false, false, "")
val lane = ide_agent_dashboard_svllm_lane(degraded_status)

verify(lane.lane_id == "svllm-inference")
# degraded readiness maps to the valid lane status "blocked"
# (valid lane statuses are ready/reviewed/blocked/unavailable).
verify(lane.status == "blocked")
```

</details>

#### svllm lane status maps offline status correctly

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val not_ready_status = svllm_status_default()
val lane = ide_agent_dashboard_svllm_lane(not_ready_status)

verify(lane.lane_id == "svllm-inference")
verify(lane.status == "unavailable")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
