# Claude Full Vim, Voice, Progress, and Agent Footer

> Checks modern SSpec parity for the command toggles and small agent components.

<!-- sdn-diagram:id=vim_voice_progress_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vim_voice_progress_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vim_voice_progress_spec -> std
vim_voice_progress_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vim_voice_progress_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Vim, Voice, Progress, and Agent Footer

Checks modern SSpec parity for the command toggles and small agent components.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/vim_voice_progress_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the command toggles and small agent components.

## Scenarios

### Claude full vim voice progress components

#### should expose vim and voice command metadata

- Read command metadata
   - Expected: vimIndexName() equals `vim`
   - Expected: vimCommandName() equals `vim`
   - Expected: voiceIndexName() equals `voice`
   - Expected: voiceCommandName() equals `voice`
   - Expected: voiceIndexDefaultProvider() equals `system`
- Resolve command behavior
   - Expected: enabled.state.enabled is true
   - Expected: applyVoiceCommand("provider whisper", state).state.provider equals `whisper`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read command metadata")
expect(vimIndexName()).to_equal("vim")
expect(vimCommandName()).to_equal("vim")
expect(voiceIndexName()).to_equal("voice")
expect(voiceCommandName()).to_equal("voice")
expect(voiceIndexDefaultProvider()).to_equal("system")

step("Resolve command behavior")
expect(vimModeMessage("on", false)).to_contain("enabled")
expect(vimModeMessage("", true)).to_contain("disabled")
val state = VoiceCommandState.new(false, "bad", "en-US")
val enabled = applyVoiceCommand("enable", state)
expect(enabled.state.enabled).to_equal(true)
expect(applyVoiceCommand("provider whisper", state).state.provider).to_equal("whisper")
expect(voiceStatus(enabled.state)).to_contain("enabled")
```

</details>

#### should render progress and navigation state

- Render agent progress
   - Expected: progressPercent(progress) equals `50`
   - Expected: isAgentProgressComplete(progress) is false
   - Expected: isAgentProgressComplete(AgentProgressState.new("build", "done", 4, 4)) is true
- Render navigation footer
   - Expected: agentNavigationFooterLabel(2, 5) equals `Agent 2 of 5`
   - Expected: canNavigatePrevious(1) is false
   - Expected: canNavigateNext(2, 5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render agent progress")
val progress = AgentProgressState.new("build", "running", 2, 4)
expect(progressPercent(progress)).to_equal(50)
expect(agentProgressLineText(progress)).to_contain("running")
expect(isAgentProgressComplete(progress)).to_equal(false)
expect(isAgentProgressComplete(AgentProgressState.new("build", "done", 4, 4))).to_equal(true)

step("Render navigation footer")
expect(agentNavigationFooterLabel(2, 5)).to_equal("Agent 2 of 5")
expect(canNavigatePrevious(1)).to_equal(false)
expect(canNavigateNext(2, 5)).to_equal(true)
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: vimIndexSourceLinesModeled() equals `11`
   - Expected: vimSourceLinesModeled() equals `38`
   - Expected: voiceIndexSourceLinesModeled() equals `20`
   - Expected: voiceSourceLinesModeled() equals `150`
   - Expected: agentProgressLineSourceLinesModeled() equals `135`
   - Expected: agentNavigationFooterSourceLinesModeled() equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(vimIndexSourceLinesModeled()).to_equal(11)
expect(vimSourceLinesModeled()).to_equal(38)
expect(voiceIndexSourceLinesModeled()).to_equal(20)
expect(voiceSourceLinesModeled()).to_equal(150)
expect(agentProgressLineSourceLinesModeled()).to_equal(135)
expect(agentNavigationFooterSourceLinesModeled()).to_equal(25)
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
