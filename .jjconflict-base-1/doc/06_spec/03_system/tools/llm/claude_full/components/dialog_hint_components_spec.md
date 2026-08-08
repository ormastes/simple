# Claude Full Dialog and Hint Components

> Checks modern SSpec parity for dialog, hint, and compact summary components.

<!-- sdn-diagram:id=dialog_hint_components_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dialog_hint_components_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dialog_hint_components_spec -> std
dialog_hint_components_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dialog_hint_components_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Dialog and Hint Components

Checks modern SSpec parity for dialog, hint, and compact summary components.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/dialog_hint_components_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for dialog, hint, and compact summary components.

## Scenarios

### Claude full dialog and hint components

#### should render progress and permission dialogs

- Render bash progress
   - Expected: bashModeProgressPercent(2, 4) equals `50`
- Render bypass and channel dialogs
   - Expected: bypassPermissionsDialogVisible(bypass) is true
   - Expected: channelDowngradeRequiresConfirm("beta", "stable") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render bash progress")
expect(bashModeProgressLabel("npm test", true)).to_contain("Running")
expect(bashModeProgressPercent(2, 4)).to_equal(50)

step("Render bypass and channel dialogs")
val bypass = BypassPermissionsState.new(true, false)
expect(bypassPermissionsDialogVisible(bypass)).to_equal(true)
expect(bypassPermissionsDialogMessage(bypass)).to_contain("confirmation")
expect(channelDowngradeRequiresConfirm("beta", "stable")).to_equal(true)
expect(channelDowngradeMessage("stable", "stable")).to_contain("No channel")
```

</details>

#### should render hint onboarding and include dialogs

- Render plugin hint
- Render Chrome and include dialogs
   - Expected: chromeOnboardingCanContinue(chrome) is true
   - Expected: externalIncludesRequiresApproval(2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render plugin hint")
expect(pluginHintMenuTitle()).to_contain("Plugin")
expect(pluginHintMenuItem("search", true)).to_contain("enabled")

step("Render Chrome and include dialogs")
val chrome = ChromeOnboardingState.new(true, true)
expect(chromeOnboardingCanContinue(chrome)).to_equal(true)
expect(chromeOnboardingStep(chrome)).to_contain("ready")
expect(externalIncludesRequiresApproval(2)).to_equal(true)
expect(externalIncludesDialogMessage(0)).to_contain("No external")
```

</details>

#### should render image summary and shortcut state

- Render clickable image
   - Expected: clickableImageRefEnabled("image.png") is true
- Render compact summary and shortcut
   - Expected: compactSummaryNeedsWarning(95, 90) is true
   - Expected: shortcutHintVisible("ctrl+x") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render clickable image")
expect(clickableImageRefEnabled("image.png")).to_equal(true)
expect(clickableImageRefLabel("image.png")).to_contain("image.png")

step("Render compact summary and shortcut")
expect(compactSummaryNeedsWarning(95, 90)).to_equal(true)
expect(compactSummaryMessage(10, 90)).to_contain("within")
expect(shortcutHintVisible("ctrl+x")).to_equal(true)
expect(shortcutHintLabel("Cut", "ctrl+x")).to_contain("ctrl+x")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: bashModeProgressSourceLinesModeled() equals `55`
   - Expected: bypassPermissionsModeDialogSourceLinesModeled() equals `86`
   - Expected: channelDowngradeDialogSourceLinesModeled() equals `101`
   - Expected: pluginHintMenuSourceLinesModeled() equals `77`
   - Expected: claudeInChromeOnboardingSourceLinesModeled() equals `120`
   - Expected: claudeMdExternalIncludesDialogSourceLinesModeled() equals `136`
   - Expected: clickableImageRefSourceLinesModeled() equals `72`
   - Expected: compactSummarySourceLinesModeled() equals `117`
   - Expected: configurableShortcutHintSourceLinesModeled() equals `56`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(bashModeProgressSourceLinesModeled()).to_equal(55)
expect(bypassPermissionsModeDialogSourceLinesModeled()).to_equal(86)
expect(channelDowngradeDialogSourceLinesModeled()).to_equal(101)
expect(pluginHintMenuSourceLinesModeled()).to_equal(77)
expect(claudeInChromeOnboardingSourceLinesModeled()).to_equal(120)
expect(claudeMdExternalIncludesDialogSourceLinesModeled()).to_equal(136)
expect(clickableImageRefSourceLinesModeled()).to_equal(72)
expect(compactSummarySourceLinesModeled()).to_equal(117)
expect(configurableShortcutHintSourceLinesModeled()).to_equal(56)
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
