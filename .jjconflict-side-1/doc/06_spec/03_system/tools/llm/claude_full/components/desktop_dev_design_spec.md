# Claude Full Desktop, Dev, and Theme Components

> Checks parity helpers for desktop handoff, upsell, development indicators, diagnostics, and theme state.

<!-- sdn-diagram:id=desktop_dev_design_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=desktop_dev_design_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

desktop_dev_design_spec -> std
desktop_dev_design_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=desktop_dev_design_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Desktop, Dev, and Theme Components

Checks parity helpers for desktop handoff, upsell, development indicators, diagnostics, and theme state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/desktop_dev_design_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks parity helpers for desktop handoff, upsell, development indicators, diagnostics, and theme state.

## Scenarios

### Claude full desktop dev and theme components

#### should render desktop handoff and upsell state

- Render desktop handoff
   - Expected: desktopHandoffEnabled(handoff) is true
   - Expected: desktopHandoffActionLabel(handoff) equals `Hand off`
- Render desktop upsell
   - Expected: desktopUpsellStartupVisible(upsell) is true
   - Expected: desktopUpsellStartupPriority(upsell) equals `high`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render desktop handoff")
val handoff = DesktopHandoffState.new(true, true, "repo", "")
expect(desktopHandoffEnabled(handoff)).to_equal(true)
expect(desktopHandoffActionLabel(handoff)).to_equal("Hand off")
expect(desktopHandoffSummary(handoff)).to_contain("repo")

step("Render desktop upsell")
val upsell = DesktopUpsellStartupState.new(false, true, 4, "Linux")
expect(desktopUpsellStartupVisible(upsell)).to_equal(true)
expect(desktopUpsellStartupPriority(upsell)).to_equal("high")
expect(desktopUpsellStartupSummary(upsell)).to_contain("Linux")
```

</details>

#### should render dev and diagnostics surfaces

- Render dev bar
   - Expected: devBarVisible(true, "development") is true
   - Expected: devBarLabel("development", "main") equals `development main`
   - Expected: devBarTone("staging") equals `warning`
- Render dev channels and diagnostics
   - Expected: devChannelsDialogCanSwitch(channel) is true
   - Expected: devChannelSummary(channel) equals `nightly inactive`
   - Expected: diagnosticSeverityTone(diagnostic) equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render dev bar")
expect(devBarVisible(true, "development")).to_equal(true)
expect(devBarLabel("development", "main")).to_equal("development main")
expect(devBarTone("staging")).to_equal("warning")

step("Render dev channels and diagnostics")
val channel = DevChannelState.new("nightly", false, "Preview")
expect(devChannelsDialogCanSwitch(channel)).to_equal(true)
expect(devChannelSummary(channel)).to_equal("nightly inactive")
val diagnostic = DiagnosticDisplayItem.new("error", "Failed", "checker")
expect(diagnosticSeverityTone(diagnostic)).to_equal("red")
expect(diagnosticDisplaySummary(diagnostic)).to_contain("checker")
```

</details>

#### should render theme state and check modeled floors

- Render themed text and provider
   - Expected: themedTextVisible(textState) is true
   - Expected: themeProviderResolvedTheme(theme) equals `dark`
- Check modeled TypeScript source floors
   - Expected: desktopHandoffSourceLinesModeled() equals `192`
   - Expected: desktopUpsellStartupSourceLinesModeled() equals `170`
   - Expected: devBarSourceLinesModeled() equals `48`
   - Expected: devChannelsDialogSourceLinesModeled() equals `104`
   - Expected: diagnosticsDisplaySourceLinesModeled() equals `94`
   - Expected: themedTextSourceLinesModeled() equals `123`
   - Expected: themeProviderSourceLinesModeled() equals `169`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render themed text and provider")
val textState = ThemedTextState.new("Hello", "accent", "bold", true)
expect(themedTextVisible(textState)).to_equal(true)
expect(themedTextClassName(textState)).to_contain("truncate")
val theme = ThemeProviderState.new("system", "dark", true, true)
expect(themeProviderResolvedTheme(theme)).to_equal("dark")
expect(themeProviderSummary(theme)).to_contain("motion-reduced")

step("Check modeled TypeScript source floors")
expect(desktopHandoffSourceLinesModeled()).to_equal(192)
expect(desktopUpsellStartupSourceLinesModeled()).to_equal(170)
expect(devBarSourceLinesModeled()).to_equal(48)
expect(devChannelsDialogSourceLinesModeled()).to_equal(104)
expect(diagnosticsDisplaySourceLinesModeled()).to_equal(94)
expect(themedTextSourceLinesModeled()).to_equal(123)
expect(themeProviderSourceLinesModeled()).to_equal(169)
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
