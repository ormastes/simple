# Claude Full Bridge and Brief Commands

> Checks modern SSpec parity for remote-control, bridge-kick, and brief commands.

<!-- sdn-diagram:id=bridge_brief_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridge_brief_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridge_brief_commands_spec -> std
bridge_brief_commands_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridge_brief_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge and Brief Commands

Checks modern SSpec parity for remote-control, bridge-kick, and brief commands.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/bridge_brief_commands_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for remote-control, bridge-kick, and brief commands.

## Scenarios

### Claude full bridge and brief commands

#### should expose remote-control command visibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = RemoteControlCommand.new(true, true)
expect(enabled.name).to_equal("remote-control")
expect(enabled.alias).to_equal("rc")
expect(enabled.hidden).to_equal(false)
expect(RemoteControlCommand.new(false, true).enabled).to_equal(false)
```

</details>

#### should model bridge-kick debug actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = callBridgeKick("status", false, BridgeDebugHandle.new())
expect(missing.message).to_contain("No bridge debug handle")
val closed = callBridgeKick("close 1002", true, BridgeDebugHandle.new())
expect(closed.handle.firedCloseCode).to_equal(1002)
val poll = callBridgeKick("poll 404", true, BridgeDebugHandle.new())
expect(poll.handle.faultMethod).to_equal("pollForWork")
expect(poll.handle.faultErrorType).to_equal("not_found_error")
val heartbeat = callBridgeKick("heartbeat 401", true, BridgeDebugHandle.new())
expect(heartbeat.handle.faultMethod).to_equal("heartbeatWork")
expect(BridgeKickCommand.new("ant").enabled).to_equal(true)
```

</details>

#### should model brief command gating and toggle

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BriefCommand.new(true, false, BriefConfig.new(true)).enabled).to_equal(true)
expect(BriefCommand.new(false, false, BriefConfig.new(true)).enabled).to_equal(false)
val gated = toggleBriefCommand(BriefAppState.new(false, false, false), false)
expect(gated.gated).to_equal(true)
val enabled = toggleBriefCommand(BriefAppState.new(false, false, false), true)
expect(enabled.state.isBriefOnly).to_equal(true)
expect(enabled.state.userMsgOptIn).to_equal(true)
expect(enabled.metaMessage).to_contain("system-reminder")
val disabled = toggleBriefCommand(enabled.state, true)
expect(disabled.state.isBriefOnly).to_equal(false)
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(remoteControlCommandSourceLinesModeled()).to_equal(26)
expect(bridgeKickSourceLinesModeled()).to_equal(200)
expect(briefSourceLinesModeled()).to_equal(130)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
