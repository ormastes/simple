# Claude Full Small Command Files

> Checks modern SSpec parity for small command descriptors and helpers.

<!-- sdn-diagram:id=command_small_files_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=command_small_files_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

command_small_files_spec -> std
command_small_files_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=command_small_files_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Small Command Files

Checks modern SSpec parity for small command descriptors and helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/command_small_files_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for small command descriptors and helpers.

## Scenarios

### Claude full small command files

#### should expose add-dir command metadata and validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = AddDirCommand.new()
expect(cmd.name).to_equal("add-dir")
expect(cmd.argumentHint).to_equal("<path>")
expect(validateDirectoryForWorkspaceModel("", false, false, "", []).resultType).to_equal("emptyPath")
val duplicate = validateDirectoryForWorkspaceModel("~/src", true, true, "/repo/src", ["/repo"])
expect(duplicate.resultType).to_equal("alreadyInWorkingDirectory")
expect(addDirHelpMessage(AddDirectoryResult.notADirectory("file", "/tmp/file"))).to_contain("parent directory")
```

</details>

#### should model advisor command decisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = AdvisorAppState.new("haiku", "")
expect(callAdvisorCommand("", state, true, true, true, true).message).to_contain("not set")
val set = callAdvisorCommand("opus", state, true, true, true, false)
expect(set.state.advisorModel).to_equal("claude-opus")
expect(set.message).to_contain("does not support advisors")
val unset = callAdvisorCommand("off", AdvisorAppState.new("sonnet", "claude-opus"), true, true, true, true)
expect(unset.state.advisorModel).to_equal("")
```

</details>

#### should expose agents and one-line command entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(callAgentsCommand(["Read", "Write"]).tools.len()).to_equal(2)
expect(callAgentsCommand(["Read"]).onExitBound).to_equal(true)
expect(AgentsCommand.new().name).to_equal("agents")
expect(autofixPrIndexSourceLinesModeled()).to_equal(1)
expect(backfillSessionsIndexSourceLinesModeled()).to_equal(1)
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(addDirCommandSourceLinesModeled()).to_equal(11)
expect(addDirValidationSourceLinesModeled()).to_equal(110)
expect(advisorCommandSourceLinesModeled()).to_equal(109)
expect(agentsCommandSourceLinesModeled()).to_equal(11)
expect(agentsIndexSourceLinesModeled()).to_equal(10)
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
