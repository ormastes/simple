# mobile_model_spec

> Claude full mobile and model command parity.

<!-- sdn-diagram:id=mobile_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mobile_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mobile_model_spec -> std
mobile_model_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mobile_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mobile_model_spec

Claude full mobile and model command parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/mobile_model_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Claude full mobile and model command parity.

## Scenarios

### Claude full mobile and model commands

#### matches mobile command metadata and URLs

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = mobileCommand()
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("mobile")
expect(command.aliases).to_equal(["ios", "android"])
expect(command.description).to_equal("Show QR code to download the Claude mobile app")
expect(command.loadPath).to_equal("./mobile.js")
expect(mobilePlatformUrl("ios")).to_equal("https://apps.apple.com/app/claude-by-anthropic/id6473753684")
expect(mobilePlatformUrl("android")).to_equal("https://play.google.com/store/apps/details?id=com.anthropic.claude")
expect(mobileQrOptions()).to_equal("type=utf8,errorCorrectionLevel=L")
expect(mobileIndexSourceLinesModeled()).to_equal(11)
```

</details>

#### models mobile QR rendering and keyboard behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val view = renderMobileQr("android", "top\n\nbottom\n")
expect(view.platform).to_equal("android")
expect(view.qrLines).to_equal(["top", "bottom"])
expect(view.controls).to_contain("tab to switch")
expect(view.tabIndex).to_equal(0)
expect(view.autoFocus).to_equal(true)

val generated = renderGeneratedMobileQr("ios")
expect(generated.qrCode).to_contain("QR(ios):https://apps.apple.com")
expect(toggleMobilePlatform("ios")).to_equal("android")
expect(toggleMobilePlatform("android")).to_equal("ios")

val switched = handleMobileKey("ios", "tab", false)
expect(switched.platform).to_equal("android")
expect(switched.done).to_equal(false)
expect(switched.prevented).to_equal(true)

val closed = handleMobileKey("android", "c", true)
expect(closed.platform).to_equal("android")
expect(closed.done).to_equal(true)
expect(closed.prevented).to_equal(true)
expect(handleMobileKey("android", "x", false).prevented).to_equal(false)
expect(mobileSourceLinesModeled()).to_equal(273)
```

</details>

#### matches model command metadata and current model output

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = modelCommand("opus", true)
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("model")
expect(command.description).to_equal("Set the AI model for Claude Code (currently Opus 4.6)")
expect(command.argumentHint).to_equal("[model]")
expect(command.immediate).to_equal(true)
expect(command.loadPath).to_equal("./model.js")
expect(modelIndexSourceLinesModeled()).to_equal(16)

val state = ModelAppState.new("sonnet", "opus", false, "high")
val current = callModel("current", state, true, true, false, true, "")
expect(current.doneMessage).to_contain("Current model: Opus 4.6 (session override from plan mode)")
expect(current.doneMessage).to_contain("Base model: Sonnet 4.6 (effort: high)")
expect(current.eventName).to_equal("tengu_model_command_inline_help")

val help = callModel("--help", state, true, true, false, true, "")
expect(help.doneMessage).to_equal("Run /model to open the model selection menu, or /model [modelName] to set the model.")
expect(help.display).to_equal("system")
```

</details>

#### sets model args, validates custom models, and blocks unavailable models

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = ModelAppState.new("sonnet", "sonnet", true, "")
val aliasSet = callModel("opus", state, true, true, false, true, "")
expect(aliasSet.nextState.mainLoopModel).to_equal("opus")
expect(aliasSet.nextState.mainLoopModelForSession).to_equal("")
expect(aliasSet.doneMessage).to_equal("Set model to Opus 4.6 · Fast mode ON · Billed as extra usage")
expect(aliasSet.eventName).to_equal("tengu_model_command_inline")
expect(aliasSet.validated).to_equal(false)

val customSet = callModel("Custom.Case.Model", state, true, true, false, true, "")
expect(customSet.nextState.mainLoopModel).to_equal("Custom.Case.Model")
expect(customSet.doneMessage).to_equal("Set model to Custom.Case.Model · Fast mode OFF")
expect(customSet.validated).to_equal(true)
expect(customSet.fastModeToggledOff).to_equal(true)

val validation = callModel("missing-model", state, true, true, false, true, "Model 'missing-model' not found")
expect(validation.doneMessage).to_equal("Model 'missing-model' not found")
expect(validation.display).to_equal("system")
expect(validation.validated).to_equal(true)

val blocked = callModel("blocked-model", state, true, true, false, true, "")
expect(blocked.doneMessage).to_equal("Model 'blocked-model' is not available. Your organization restricts model selection.")
expect(blocked.display).to_equal("system")
```

</details>

#### models 1M access, picker cancel/select, and source floors

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = ModelAppState.new("opus", "", true, "")
val opusBlocked = callModel("opus[1m]", state, false, true, false, true, "")
expect(opusBlocked.doneMessage).to_contain("Opus 4.6 with 1M context is not available")
val sonnetBlocked = callModel("sonnet-4-6[1m]", state, true, false, false, true, "")
expect(sonnetBlocked.doneMessage).to_contain("Sonnet 4.6 with 1M context is not available")
expect(isOpus1mUnavailable("opus[1m]", false, false)).to_equal(true)
expect(isSonnet1mUnavailable("sonnet-4-6[1m]", false)).to_equal(true)
expect(isKnownAlias(" Opus ")).to_equal(true)
expect(renderModelLabel("")).to_equal("Default (default)")

val picker = modelPickerRendered(state, true, true)
expect(picker.rendered).to_equal("picker:fast-notice")
val cancel = cancelModelPicker(state)
expect(cancel.doneMessage).to_equal("Kept model as Opus 4.6")
expect(cancel.display).to_equal("system")
val selected = selectModelFromPicker("haiku", "low", state, true, false)
expect(selected.doneMessage).to_equal("Set model to Haiku with low effort · Fast mode OFF")
expect(selected.eventName).to_equal("tengu_model_command_menu")
expect(modelSourceLinesModeled()).to_equal(296)
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
