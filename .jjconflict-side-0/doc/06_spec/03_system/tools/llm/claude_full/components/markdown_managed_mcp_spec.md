# Claude Full Markdown, Managed Settings, and MCP Components

> Modern SSpec coverage for the medium/small parity batch after LogoV2.

<!-- sdn-diagram:id=markdown_managed_mcp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=markdown_managed_mcp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

markdown_managed_mcp_spec -> std
markdown_managed_mcp_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=markdown_managed_mcp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Markdown, Managed Settings, and MCP Components

Modern SSpec coverage for the medium/small parity batch after LogoV2.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/markdown_managed_mcp_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Modern SSpec coverage for the medium/small parity batch after LogoV2.

## Scenarios

### Claude full markdown managed settings and MCP parity

#### should render welcome and LSP recommendation decisions

- Render Apple terminal light welcome
   - Expected: welcomeV2Palette(welcome) equals `apple-light`
- Render LSP recommendation options
   - Expected: lspRecommendationOptions(lsp.plugin_name).len() equals `4`
   - Expected: lspRecommendationResponseForSelect("disable") equals `disable`
   - Expected: lspRecommendationAutoDismissResponse() equals `no`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render Apple terminal light welcome")
val welcome = WelcomeV2State.new("light", "Apple_Terminal", "2.0.0", "")
expect(welcomeV2Palette(welcome)).to_equal("apple-light")
expect(welcomeV2Summary(welcome)).to_contain("Welcome to Claude Code")

step("Render LSP recommendation options")
val lsp = LspRecommendationState.new("simple-lsp", "Simple language", ".spl", "yes")
expect(lspRecommendationOptions(lsp.plugin_name).len()).to_equal(4)
expect(lspRecommendationResponseForSelect("disable")).to_equal("disable")
expect(lspRecommendationAutoDismissResponse()).to_equal("no")
```

</details>

#### should detect and format managed settings risk

- Extract dangerous managed settings
   - Expected: hasDangerousSettings(dangerous) is true
   - Expected: formatDangerousSettingsList(dangerous).len() equals `3`
   - Expected: hasDangerousSettingsChanged(oldSettings, newSettings) is true
- Render managed settings dialog
   - Expected: managedSettingsDialogChoiceResponse(dialog.selected_value) equals `reject`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Extract dangerous managed settings")
val oldSettings = ManagedSettingsInput.new("", ["PATH"], 0)
val newSettings = ManagedSettingsInput.new("/bin/sh", ["PATH", "LD_PRELOAD"], 1)
val dangerous = extractDangerousSettings(newSettings)
expect(hasDangerousSettings(dangerous)).to_equal(true)
expect(formatDangerousSettingsList(dangerous).len()).to_equal(3)
expect(hasDangerousSettingsChanged(oldSettings, newSettings)).to_equal(true)

step("Render managed settings dialog")
val dialog = ManagedSettingsSecurityDialogState.new(newSettings, true, "Ctrl-C", "exit")
expect(managedSettingsDialogChoiceResponse(dialog.selected_value)).to_equal("reject")
expect(managedSettingsDialogSummary(dialog)).to_contain("items=3")
```

</details>

#### should render markdown table and MCP summaries

- Render markdown modes
   - Expected: markdownRenderMode(md) equals `table`
- Render markdown table layout
   - Expected: markdownTableShouldUseVertical(table) is false
- Render MCP capabilities
   - Expected: mcpComponentExports().len() equals `8`
   - Expected: mcpTypeExports().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render markdown modes")
val md = MarkdownRenderState.new("<prompt>| A | B |</prompt>", false, false, "dark")
expect(markdownRenderMode(md)).to_equal("table")
expect(markdownSummary(md)).to_contain("table")

step("Render markdown table layout")
val table = MarkdownTableState.new(["Name", "Value"], [["alpha", "beta"]], 80)
expect(markdownTableShouldUseVertical(table)).to_equal(false)
expect(markdownTableSummary(table)).to_contain("grid")

step("Render MCP capabilities")
val capabilities = CapabilitiesCounts.new(2, 1, 0)
expect(capabilitiesSummary(capabilities)).to_contain("tools")
expect(mcpComponentExports().len()).to_equal(8)
expect(mcpTypeExports().len()).to_equal(3)
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: welcomeV2SourceLinesModeled() equals `432`
   - Expected: lspRecommendationSourceLinesModeled() equals `87`
   - Expected: managedSettingsSecurityDialogSourceLinesModeled() equals `148`
   - Expected: managedSettingsUtilsSourceLinesModeled() equals `144`
   - Expected: markdownTableSourceLinesModeled() equals `321`
   - Expected: markdownSourceLinesModeled() equals `235`
   - Expected: capabilitiesSectionSourceLinesModeled() equals `60`
   - Expected: mcpIndexSourceLinesModeled() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(welcomeV2SourceLinesModeled()).to_equal(432)
expect(lspRecommendationSourceLinesModeled()).to_equal(87)
expect(managedSettingsSecurityDialogSourceLinesModeled()).to_equal(148)
expect(managedSettingsUtilsSourceLinesModeled()).to_equal(144)
expect(markdownTableSourceLinesModeled()).to_equal(321)
expect(markdownSourceLinesModeled()).to_equal(235)
expect(capabilitiesSectionSourceLinesModeled()).to_equal(60)
expect(mcpIndexSourceLinesModeled()).to_equal(9)
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
