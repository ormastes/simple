# Claude Full Tool Name Constants

> Mirrors one-line Claude tool constant files so the strict full-parity matrix

<!-- sdn-diagram:id=tool_name_constants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tool_name_constants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tool_name_constants_spec -> std
tool_name_constants_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tool_name_constants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Tool Name Constants

Mirrors one-line Claude tool constant files so the strict full-parity matrix

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/tool_name_constants_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors one-line Claude tool constant files so the strict full-parity matrix
has executable evidence for the literal tool names used by command dispatch.

## Scenarios

### Claude full tool name constants

#### should expose plan and worktree tool names

- Read the tool constants mapped from Claude tool constant files
   - Expected: ENTER_PLAN_MODE_TOOL_NAME equals `EnterPlanMode`
   - Expected: ENTER_WORKTREE_TOOL_NAME equals `EnterWorktree`
   - Expected: EXIT_WORKTREE_TOOL_NAME equals `ExitWorktree`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the tool constants mapped from Claude tool constant files")
expect(ENTER_PLAN_MODE_TOOL_NAME).to_equal("EnterPlanMode")
expect(ENTER_WORKTREE_TOOL_NAME).to_equal("EnterWorktree")
expect(EXIT_WORKTREE_TOOL_NAME).to_equal("ExitWorktree")
```

</details>

#### should expose message and skill tool names

- Read the remaining tool constants in this batch
   - Expected: SEND_MESSAGE_TOOL_NAME equals `SendMessage`
   - Expected: SKILL_TOOL_NAME equals `Skill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the remaining tool constants in this batch")
expect(SEND_MESSAGE_TOOL_NAME).to_equal("SendMessage")
expect(SKILL_TOOL_NAME).to_equal("Skill")
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
