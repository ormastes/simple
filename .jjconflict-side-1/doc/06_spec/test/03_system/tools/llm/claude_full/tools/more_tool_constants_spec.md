# Claude Full Additional Tool Constants

> Mirrors the next small Claude tool-name and render-interval constant files.

<!-- sdn-diagram:id=more_tool_constants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=more_tool_constants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

more_tool_constants_spec -> std
more_tool_constants_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=more_tool_constants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Additional Tool Constants

Mirrors the next small Claude tool-name and render-interval constant files.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/more_tool_constants_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors the next small Claude tool-name and render-interval constant files.

## Scenarios

### Claude full additional constants

#### should expose exit-plan and notebook tool names

- Read the constants mapped from ExitPlanModeTool and NotebookEditTool
   - Expected: EXIT_PLAN_MODE_TOOL_NAME equals `ExitPlanMode`
   - Expected: EXIT_PLAN_MODE_V2_TOOL_NAME equals `ExitPlanMode`
   - Expected: NOTEBOOK_EDIT_TOOL_NAME equals `NotebookEdit`
   - Expected: notebookEditToolName() equals `NotebookEdit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the constants mapped from ExitPlanModeTool and NotebookEditTool")
expect(EXIT_PLAN_MODE_TOOL_NAME).to_equal("ExitPlanMode")
expect(EXIT_PLAN_MODE_V2_TOOL_NAME).to_equal("ExitPlanMode")
expect(NOTEBOOK_EDIT_TOOL_NAME).to_equal("NotebookEdit")
expect(notebookEditToolName()).to_equal("NotebookEdit")
```

</details>

#### should expose shell tool names and frame interval

- Read the shell tool constants and render frame interval
   - Expected: BASH_TOOL_NAME equals `Bash`
   - Expected: bashToolName() equals `Bash`
   - Expected: POWERSHELL_TOOL_NAME equals `PowerShell`
   - Expected: powerShellToolName() equals `PowerShell`
   - Expected: FRAME_INTERVAL_MS equals `16`
   - Expected: frameIntervalMs() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the shell tool constants and render frame interval")
expect(BASH_TOOL_NAME).to_equal("Bash")
expect(bashToolName()).to_equal("Bash")
expect(POWERSHELL_TOOL_NAME).to_equal("PowerShell")
expect(powerShellToolName()).to_equal("PowerShell")
expect(FRAME_INTERVAL_MS).to_equal(16)
expect(frameIntervalMs()).to_equal(16)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
