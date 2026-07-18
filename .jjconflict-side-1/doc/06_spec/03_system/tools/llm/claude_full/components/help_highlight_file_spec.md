# Claude Full Help, Highlighted Code, and File Link Components

> Checks modern SSpec parity for the smaller help/highlight/file components.

<!-- sdn-diagram:id=help_highlight_file_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=help_highlight_file_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

help_highlight_file_spec -> std
help_highlight_file_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=help_highlight_file_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Help, Highlighted Code, and File Link Components

Checks modern SSpec parity for the smaller help/highlight/file components.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/help_highlight_file_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the smaller help/highlight/file components.

## Scenarios

### Claude full help highlighted code and file components

#### should render file rejected and path link states

- Render rejected edit message
   - Expected: fileEditRejectedAction(rejected) equals `Revise edit`
- Render file path link
   - Expected: filePathLinkHref("src/app.spl", 12) equals `src/app.spl:12`
   - Expected: filePathLinkTitle("", 0) equals `Open unknown file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render rejected edit message")
val rejected = FileEditRejectedState.new("src/app.spl", "Denied", "Ada", true)
expect(fileEditRejectedAction(rejected)).to_equal("Revise edit")
expect(fileEditRejectedSummary(rejected)).to_contain("Ada")

step("Render file path link")
expect(filePathLinkHref("src/app.spl", 12)).to_equal("src/app.spl:12")
expect(filePathLinkTitle("", 0)).to_equal("Open unknown file")
```

</details>

#### should render help commands and tabs

- Render help command
   - Expected: helpCommandMatches(command, "help") is true
   - Expected: helpCommandsCountLabel(2) equals `2 command(s)`
- Render HelpV2 state
   - Expected: helpV2Visible(help) is true
   - Expected: helpV2SwitchTab(help, "general").tab equals `general`
   - Expected: helpGeneralSummary("keys") equals `Help for keys`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render help command")
val command = HelpCommand.new("/help", "Open help", "ctrl+h")
expect(helpCommandSummary(command)).to_contain("Open help")
expect(helpCommandMatches(command, "help")).to_equal(true)
expect(helpCommandsCountLabel(2)).to_equal("2 command(s)")

step("Render HelpV2 state")
val help = HelpV2State.new(true, "commands", "git")
expect(helpV2Visible(help)).to_equal(true)
expect(helpV2Summary(help)).to_contain("git")
expect(helpV2SwitchTab(help, "general").tab).to_equal("general")
expect(helpGeneralSummary("keys")).to_equal("Help for keys")
```

</details>

#### should render highlighted code states

- Render fallback code
   - Expected: highlightFallbackLanguage(fallback) equals `text`
   - Expected: highlightFallbackLineCount(fallback) equals `2`
- Render highlighted code
   - Expected: highlightedCodeCanHighlight(code) is true
   - Expected: highlightedCodeRenderMode(code) equals `highlighted`
   - Expected: highlightedCodeSummary(code) equals `simple dark`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render fallback code")
val fallback = HighlightFallbackState.new("one\ntwo", "", true)
expect(highlightFallbackLanguage(fallback)).to_equal("text")
expect(highlightFallbackLineCount(fallback)).to_equal(2)
expect(highlightFallbackRender(fallback)).to_contain("lines=2")

step("Render highlighted code")
val code = HighlightedCodeState.new("val x = 1", "simple", "", false)
expect(highlightedCodeCanHighlight(code)).to_equal(true)
expect(highlightedCodeRenderMode(code)).to_equal("highlighted")
expect(highlightedCodeSummary(code)).to_equal("simple dark")
```

</details>

#### should check modeled TypeScript source floors

- Read source line helpers
   - Expected: fileEditToolUseRejectedMessageSourceLinesModeled() equals `169`
   - Expected: filePathLinkSourceLinesModeled() equals `42`
   - Expected: helpCommandsSourceLinesModeled() equals `81`
   - Expected: helpGeneralSourceLinesModeled() equals `22`
   - Expected: helpV2SourceLinesModeled() equals `183`
   - Expected: highlightFallbackSourceLinesModeled() equals `192`
   - Expected: highlightedCodeSourceLinesModeled() equals `189`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source line helpers")
expect(fileEditToolUseRejectedMessageSourceLinesModeled()).to_equal(169)
expect(filePathLinkSourceLinesModeled()).to_equal(42)
expect(helpCommandsSourceLinesModeled()).to_equal(81)
expect(helpGeneralSourceLinesModeled()).to_equal(22)
expect(helpV2SourceLinesModeled()).to_equal(183)
expect(highlightFallbackSourceLinesModeled()).to_equal(192)
expect(highlightedCodeSourceLinesModeled()).to_equal(189)
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
