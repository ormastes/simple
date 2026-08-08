# Claude Full Thinkback Command

> Checks thinkback command parity with modern SSpec coverage.

<!-- sdn-diagram:id=thinkback_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thinkback_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thinkback_command_spec -> std
thinkback_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thinkback_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Thinkback Command

Checks thinkback command parity with modern SSpec coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/thinkback_command_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks thinkback command parity with modern SSpec coverage.

## Scenarios

### Claude full thinkback command

#### normalizes topics and empty input

- Normalize topic text
   - Expected: normalizeThinkbackTopic("  Release Plan  ") equals `release plan`
- Use the default empty topic
   - Expected: normalizeThinkbackTopic("   ") equals `recent conversation`
   - Expected: call("   ").topic equals `recent conversation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Normalize topic text")
expect(normalizeThinkbackTopic("  Release Plan  ")).to_equal("release plan")

step("Use the default empty topic")
expect(normalizeThinkbackTopic("   ")).to_equal("recent conversation")
expect(call("   ").topic).to_equal("recent conversation")
```

</details>

#### renders replay and summary text

- Render summary
   - Expected: thinkbackSummaryText("Feature Flags") equals `Thinkback summary: feature flags`
- Render replay
   - Expected: replay.status equals `replay`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render summary")
expect(thinkbackSummaryText("Feature Flags")).to_equal("Thinkback summary: feature flags")
expect(call("Feature Flags").summary).to_contain("feature flags")

step("Render replay")
val replay = callThinkback("Incident Review", "replay")
expect(replay.status).to_equal("replay")
expect(replay.replay).to_contain("incident review")
expect(thinkbackReplayText("Incident Review")).to_start_with("Replay prior context")
```

</details>

#### models selection and installer state

- Select a supported action
   - Expected: selected.selectedAction equals `replay`
- Install and disable states
   - Expected: isDisabled(disabled) is true
   - Expected: ThinkbackInstaller(disabled).status equals `installed`
   - Expected: ThinkbackInstaller(disabled).state.installed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select a supported action")
val state = ThinkbackState.new("Roadmap", "", true, false, ["older"])
val selected = selectThinkbackAction(state, " replay ")
expect(selected.selectedAction).to_equal("replay")
expect(selected.history).to_contain("older")

step("Install and disable states")
val disabled = ThinkbackState.new("Roadmap", "summary", false, true, [])
expect(isDisabled(disabled)).to_equal(true)
expect(errorMsg(disabled)).to_contain("not installed")
expect(ThinkbackInstaller(disabled).status).to_equal("installed")
expect(ThinkbackInstaller(disabled).state.installed).to_equal(true)
```

</details>

#### keeps metadata and source floors visible

- Check command metadata
   - Expected: thinkbackIndexName() equals `thinkback`
   - Expected: getMarketplaceName() equals `thinkback`
   - Expected: getMarketplaceRepo() equals `anthropics/thinkback`
   - Expected: getPluginId() equals `anthropic/thinkback`
   - Expected: getThinkbackSkillDir() equals `skills/thinkback`
   - Expected: thinkbackPlugin() equals `anthropic/thinkback`
- Check modeled source line helpers
   - Expected: thinkbackIndexSourceLinesModeled() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check command metadata")
expect(thinkbackIndexName()).to_equal("thinkback")
expect(thinkbackPrompt("latest decision")).to_contain("latest decision")
expect(getMarketplaceName()).to_equal("thinkback")
expect(getMarketplaceRepo()).to_equal("anthropics/thinkback")
expect(getPluginId()).to_equal("anthropic/thinkback")
expect(getThinkbackSkillDir()).to_equal("skills/thinkback")
expect(thinkbackPlugin()).to_equal("anthropic/thinkback")

step("Check modeled source line helpers")
expect(thinkbackIndexSourceLinesModeled()).to_equal(13)
expect(thinkbackSourceLinesModeled()).to_be_greater_than(552)
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
