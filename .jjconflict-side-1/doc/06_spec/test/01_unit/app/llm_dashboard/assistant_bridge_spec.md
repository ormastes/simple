# Assistant Bridge Specification

> <details>

<!-- sdn-diagram:id=assistant_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assistant_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assistant_bridge_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assistant_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Bridge Specification

## Scenarios

### assistant dashboard bridge

#### keeps replay-only projections read-only and blocks control routing

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = assistant_bridge_default_policy()
val projection = assistant_bridge_projection_from_empty("session-replay", policy, 1_000_000_000)
val decision = assistant_bridge_route_action(projection, control_action_kind())

expect(projection.read_only).to_equal(true)
expect(projection.freshness.state).to_equal("replay")
expect(projection.live_controls_enabled).to_equal(false)
expect(decision.allowed).to_equal(false)
expect(decision.route_target).to_equal("blocked")
expect(decision.policy_state).to_equal("replay")
```

</details>

#### routes fresh live projections back to the assistant core

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = assistant_bridge_default_policy()
val snapshot = make_snapshot("session-live", policy.source_of_truth, 2_000_000_000, 2_000_000_000, true)
val projection = assistant_bridge_projection_from_snapshot(snapshot, policy, 2_000_000_100)
val decision = assistant_bridge_route_action(projection, control_action_kind())

expect(projection.read_only).to_equal(false)
expect(projection.freshness.state).to_equal("fresh")
expect(projection.live_controls_enabled).to_equal(true)
expect(projection.freshness.can_route_actions).to_equal(true)
expect(decision.allowed).to_equal(true)
expect(decision.route_target).to_equal("assistant_core")
expect(decision.policy_state).to_equal("live")
```

</details>

#### keeps stale and degraded projections blocked until refreshed

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = assistant_bridge_default_policy()
val stale_snapshot = make_snapshot("session-stale", policy.source_of_truth, 900_000_000, 900_000_000, true)
val stale_projection = assistant_bridge_projection_from_snapshot(stale_snapshot, policy, 940_000_000)
val stale_decision = assistant_bridge_route_action(stale_projection, control_action_kind())

expect(stale_projection.freshness.state).to_equal("stale")
expect(stale_projection.read_only).to_equal(true)
expect(stale_projection.freshness.should_refresh).to_equal(true)
expect(stale_decision.allowed).to_equal(false)
expect(stale_decision.route_target).to_equal("blocked")
expect(stale_decision.should_refresh).to_equal(true)

val degraded_snapshot = make_snapshot("session-degraded", policy.source_of_truth, 700_000_000, 700_000_000, true)
val degraded_projection = assistant_bridge_projection_from_snapshot(degraded_snapshot, policy, 830_000_000)
val degraded_decision = assistant_bridge_route_action(degraded_projection, control_action_kind())

expect(degraded_projection.freshness.state).to_equal("degraded")
expect(degraded_projection.freshness.is_degraded).to_equal(true)
expect(degraded_projection.read_only).to_equal(true)
expect(degraded_projection.freshness.should_refresh).to_equal(true)
expect(degraded_decision.allowed).to_equal(false)
expect(degraded_decision.route_target).to_equal("blocked")
expect(degraded_decision.should_refresh).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_dashboard/assistant_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant dashboard bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
