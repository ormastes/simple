# Claude Full Bootstrap State

> Checks modern SSpec parity for the bootstrap state capsule.

<!-- sdn-diagram:id=state_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=state_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

state_spec -> std
state_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=state_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bootstrap State

Checks modern SSpec parity for the bootstrap state capsule.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bootstrap/state_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the bootstrap state capsule.

## Scenarios

### Claude full bootstrap state

#### should track session identity and roots

- var state = ClaudeFullState new
- state = state setProjectRoot
   - Expected: state.originalCwd equals `/repo`
   - Expected: state.projectRoot equals `/repo/root`
   - Expected: state.cwd equals `/repo/work`
- state = state regenerateSessionId
   - Expected: state.parentSessionId equals `s1`
   - Expected: state.sessionId equals `s2`
- state = state switchSession
   - Expected: state.sessionProjectDir equals `/sessions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = ClaudeFullState.new("/repo", "s1")
state = state.setProjectRoot("/repo/root").setCwdState("/repo/work")
expect(state.originalCwd).to_equal("/repo")
expect(state.projectRoot).to_equal("/repo/root")
expect(state.cwd).to_equal("/repo/work")
state = state.regenerateSessionId("s2")
expect(state.parentSessionId).to_equal("s1")
expect(state.sessionId).to_equal("s2")
state = state.switchSession("s3", "s2", "/sessions")
expect(state.sessionProjectDir).to_equal("/sessions")
```

</details>

#### should accumulate costs durations lines and model tokens

- var state = ClaudeFullState new
- state = state addToTotalDurationState
- state = state addToTotalCostState
- state = state addModelUsage
- state = state snapshotOutputTokensForTurn
- state = state addModelUsage
   - Expected: state.totalAPIDuration equals `10`
   - Expected: state.totalToolDuration equals `5`
   - Expected: state.turnHookCount equals `1`
   - Expected: state.totalCostUSD equals `25`
   - Expected: state.totalLinesAdded equals `4`
   - Expected: state.getTotalInputTokens() equals `10`
   - Expected: state.getTurnOutputTokens() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = ClaudeFullState.new("/repo", "s1")
state = state.addToTotalDurationState(10, 7).addToToolDuration(5).addToTurnHookDuration(3).addToTurnClassifierDuration(2)
state = state.addToTotalCostState(25).addToTotalLinesChanged(4, 1)
state = state.addModelUsage("haiku", ModelUsage.new().add(10, 2, 3, 4, 1))
state = state.snapshotOutputTokensForTurn(100)
state = state.addModelUsage("haiku", ModelUsage.new().add(0, 5, 0, 0, 0))
expect(state.totalAPIDuration).to_equal(10)
expect(state.totalToolDuration).to_equal(5)
expect(state.turnHookCount).to_equal(1)
expect(state.totalCostUSD).to_equal(25)
expect(state.totalLinesAdded).to_equal(4)
expect(state.getTotalInputTokens()).to_equal(10)
expect(state.getTurnOutputTokens()).to_equal(5)
```

</details>

#### should handle providers flags hooks and auth preferences

- var state = ClaudeFullState new
- state = state setTelemetryProviders
- state = state setInteractive
- state = state setAllowedSettingSources
- state = state setRegisteredHooks
   - Expected: state.meterSet is true
   - Expected: state.getIsNonInteractiveSession() is true
   - Expected: state.clientType equals `sdk`
   - Expected: state.preferThirdPartyAuthentication() is true
   - Expected: state.registeredHooks[0].eventName equals `PreToolUse`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = ClaudeFullState.new("/repo", "s1")
state = state.setTelemetryProviders(true, true, false, true, false)
state = state.setInteractive(false).setClientType("sdk").setSessionSource("remote")
state = state.setAllowedSettingSources(["project"])
state = state.setRegisteredHooks("PreToolUse", ["matcher"])
expect(state.meterSet).to_equal(true)
expect(state.getIsNonInteractiveSession()).to_equal(true)
expect(state.clientType).to_equal("sdk")
expect(state.preferThirdPartyAuthentication()).to_equal(true)
expect(state.registeredHooks[0].eventName).to_equal("PreToolUse")
```

</details>

#### should manage session-only teams cron channels and skills

- var state = ClaudeFullState new
- state = state setSessionFlags
- state = state addSessionCronTask
- state = state addSessionCreatedTeam
- state = state setAllowedChannels
- state = state addInvokedSkill
   - Expected: state.sessionBypassPermissionsMode is true
   - Expected: state.sessionCronTasks.len() equals `1`
   - Expected: state.sessionCreatedTeams.len() equals `1`
   - Expected: state.hasDevChannels is true
   - Expected: state.invokedSkills[0].key equals `agent-1:impl`
- state = state removeSessionCronTasks
   - Expected: state.sessionCronTasks.len() equals `0`
   - Expected: state.sessionCreatedTeams.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = ClaudeFullState.new("/repo", "s1")
state = state.setSessionFlags(true, true, true, false)
state = state.addSessionCronTask(SessionCronTask.new("c1", "* * * * *", "echo ok"))
state = state.addSessionCreatedTeam("team-a").addSessionCreatedTeam("team-a")
state = state.setAllowedChannels([ChannelEntry.plugin("plugin-a", "market", true), ChannelEntry.server("srv", false)])
state = state.addInvokedSkill("impl", "/skills/impl", "content", 10, "agent-1")
expect(state.sessionBypassPermissionsMode).to_equal(true)
expect(state.sessionCronTasks.len()).to_equal(1)
expect(state.sessionCreatedTeams.len()).to_equal(1)
expect(state.hasDevChannels).to_equal(true)
expect(state.invokedSkills[0].key).to_equal("agent-1:impl")
state = state.removeSessionCronTasks(["c1"]).removeSessionCreatedTeam("team-a")
expect(state.sessionCronTasks.len()).to_equal(0)
expect(state.sessionCreatedTeams.len()).to_equal(0)
```

</details>

#### should reset test state and expose source size

- var state = ClaudeFullState new
- state = state addError
   - Expected: state.inMemoryErrorLog.len() equals `1`
   - Expected: state.slowOperations[0].durationMs equals `42`
   - Expected: state.resetStateForTests().isRemoteMode is false
   - Expected: bootstrapStateSourceLinesModeled() equals `1758`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = ClaudeFullState.new("/repo", "s1")
state = state.addError("e", "t").addSlowOperation("op", 42, 9).setRemoteMode(true)
expect(state.inMemoryErrorLog.len()).to_equal(1)
expect(state.slowOperations[0].durationMs).to_equal(42)
expect(state.resetStateForTests().isRemoteMode).to_equal(false)
expect(bootstrapStateSourceLinesModeled()).to_equal(1758)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
