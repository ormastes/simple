# Claude Full Task And Team Tool Constants

> Mirrors one-line Claude task/team tool constant files so each mapped full-parity

<!-- sdn-diagram:id=task_team_constants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_team_constants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_team_constants_spec -> std
task_team_constants_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_team_constants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Task And Team Tool Constants

Mirrors one-line Claude task/team tool constant files so each mapped full-parity

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/task_team_constants_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors one-line Claude task/team tool constant files so each mapped full-parity
target has executable literal evidence.

## Scenarios

### Claude full task and team tool constants

#### should expose task tool names

- Read the task tool constants mapped from Claude
   - Expected: TASK_CREATE_TOOL_NAME equals `TaskCreate`
   - Expected: TASK_GET_TOOL_NAME equals `TaskGet`
   - Expected: TASK_LIST_TOOL_NAME equals `TaskList`
   - Expected: TASK_OUTPUT_TOOL_NAME equals `TaskOutput`
   - Expected: TASK_UPDATE_TOOL_NAME equals `TaskUpdate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the task tool constants mapped from Claude")
expect(TASK_CREATE_TOOL_NAME).to_equal("TaskCreate")
expect(TASK_GET_TOOL_NAME).to_equal("TaskGet")
expect(TASK_LIST_TOOL_NAME).to_equal("TaskList")
expect(TASK_OUTPUT_TOOL_NAME).to_equal("TaskOutput")
expect(TASK_UPDATE_TOOL_NAME).to_equal("TaskUpdate")
```

</details>

#### should expose team, todo, and tool-search names

- Read the remaining constants in this batch
   - Expected: TEAM_CREATE_TOOL_NAME equals `TeamCreate`
   - Expected: TEAM_DELETE_TOOL_NAME equals `TeamDelete`
   - Expected: TODO_WRITE_TOOL_NAME equals `TodoWrite`
   - Expected: TOOL_SEARCH_TOOL_NAME equals `ToolSearch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the remaining constants in this batch")
expect(TEAM_CREATE_TOOL_NAME).to_equal("TeamCreate")
expect(TEAM_DELETE_TOOL_NAME).to_equal("TeamDelete")
expect(TODO_WRITE_TOOL_NAME).to_equal("TodoWrite")
expect(TOOL_SEARCH_TOOL_NAME).to_equal("ToolSearch")
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
