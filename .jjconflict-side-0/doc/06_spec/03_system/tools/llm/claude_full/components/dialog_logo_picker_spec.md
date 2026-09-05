# Claude Full Dialog, Picker, and Logo Components

> Checks modern SSpec parity for idle/invalid dialogs, keybinding/language helpers, and small LogoV2 helpers.

<!-- sdn-diagram:id=dialog_logo_picker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dialog_logo_picker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dialog_logo_picker_spec -> std
dialog_logo_picker_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dialog_logo_picker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Dialog, Picker, and Logo Components

Checks modern SSpec parity for idle/invalid dialogs, keybinding/language helpers, and small LogoV2 helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/dialog_logo_picker_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for idle/invalid dialogs, keybinding/language helpers, and small LogoV2 helpers.

## Scenarios

### Claude full dialog picker and small logo components

#### should render idle and interrupted states

- Render idle return dialog
   - Expected: idleReturnAction(idle) equals `Resume work`
- Render interrupted message
   - Expected: interruptedByUserMessage() equals `Interrupted by user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render idle return dialog")
val idle = IdleReturnState.new(true, 12, true, "main")
expect(idleReturnAction(idle)).to_equal("Resume work")
expect(idleReturnSummary(idle)).to_contain("idle=12")

step("Render interrupted message")
expect(interruptedByUserMessage()).to_equal("Interrupted by user")
```

</details>

#### should render invalid settings and config dialogs

- Render invalid config
   - Expected: invalidConfigAction(config) equals `Open config`
- Render invalid settings
   - Expected: invalidSettingsTitle(settings) equals `Invalid setting theme`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render invalid config")
val config = InvalidConfigState.new(true, "settings.json", "bad json", true)
expect(invalidConfigAction(config)).to_equal("Open config")
expect(invalidConfigSummary(config)).to_contain("bad json")

step("Render invalid settings")
val settings = InvalidSettingsState.new(true, "theme", "")
expect(invalidSettingsTitle(settings)).to_equal("Invalid setting theme")
expect(invalidSettingsSummary(settings)).to_contain("could not be loaded")
```

</details>

#### should render keybinding language and logo states

- Render keybinding and language helpers
   - Expected: keybindingWarningTone(4) equals `error`
   - Expected: languagePickerVisible(picker) is true
- Render LogoV2 helpers
   - Expected: animatedAsteriskFrame(2) equals `*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render keybinding and language helpers")
expect(keybindingWarningTone(4)).to_equal("error")
expect(keybindingWarningSummary(2, "global")).to_contain("global")
val picker = LanguagePickerState.new("", true, "en")
expect(languagePickerVisible(picker)).to_equal(true)
expect(languagePickerSummary(picker)).to_contain("en")

step("Render LogoV2 helpers")
expect(animatedAsteriskFrame(2)).to_equal("*")
val clawd = AnimatedClawdState.new(1, "beta", true)
expect(animatedClawdLabel(clawd)).to_contain("beta")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: idleReturnDialogSourceLinesModeled() equals `117`
   - Expected: interruptedByUserSourceLinesModeled() equals `14`
   - Expected: invalidConfigDialogSourceLinesModeled() equals `155`
   - Expected: invalidSettingsDialogSourceLinesModeled() equals `88`
   - Expected: keybindingWarningsSourceLinesModeled() equals `54`
   - Expected: languagePickerSourceLinesModeled() equals `85`
   - Expected: animatedAsteriskSourceLinesModeled() equals `49`
   - Expected: animatedClawdSourceLinesModeled() equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(idleReturnDialogSourceLinesModeled()).to_equal(117)
expect(interruptedByUserSourceLinesModeled()).to_equal(14)
expect(invalidConfigDialogSourceLinesModeled()).to_equal(155)
expect(invalidSettingsDialogSourceLinesModeled()).to_equal(88)
expect(keybindingWarningsSourceLinesModeled()).to_equal(54)
expect(languagePickerSourceLinesModeled()).to_equal(85)
expect(animatedAsteriskSourceLinesModeled()).to_equal(49)
expect(animatedClawdSourceLinesModeled()).to_equal(123)
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
