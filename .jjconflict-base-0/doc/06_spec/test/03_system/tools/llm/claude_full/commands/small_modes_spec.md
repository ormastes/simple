# Claude Full Small Mode Commands

> Checks modern SSpec parity for output-style, passes, permissions, and plan.

<!-- sdn-diagram:id=small_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=small_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

small_modes_spec -> std
small_modes_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=small_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Small Mode Commands

Checks modern SSpec parity for output-style, passes, permissions, and plan.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/small_modes_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for output-style, passes, permissions, and plan.

## Scenarios

### Claude full small mode commands

#### should expose small descriptor names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(outputStyleIndexCommandName()).to_equal("output-style")
expect(passesIndexCommandName()).to_equal("passes")
expect(permissionsIndexCommandName()).to_equal("permissions")
```

</details>

#### should model plan state changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = PlanCommandState.new("default", false)
expect(planIndexCommandName()).to_equal("plan")
expect(enterPlanMode(state).readonly).to_equal(true)
expect(planModeMessage(enterPlanMode(state))).to_contain("enabled")
expect(leavePlanMode(enterPlanMode(state)).mode).to_equal("default")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(outputStyleIndexSourceLinesModeled()).to_equal(11)
expect(passesSourceLinesModeled()).to_equal(23)
expect(passesIndexSourceLinesModeled()).to_equal(22)
expect(permissionsSourceLinesModeled()).to_equal(9)
expect(permissionsIndexSourceLinesModeled()).to_equal(11)
expect(planSourceLinesModeled()).to_equal(121)
expect(planIndexSourceLinesModeled()).to_equal(11)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
