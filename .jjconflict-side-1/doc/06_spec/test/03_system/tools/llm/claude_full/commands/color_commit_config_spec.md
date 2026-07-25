# Claude Full Color, Commit, and Config Commands

> Checks modern SSpec parity for the small command cluster.

<!-- sdn-diagram:id=color_commit_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_commit_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_commit_config_spec -> std
color_commit_config_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_commit_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Color, Commit, and Config Commands

Checks modern SSpec parity for the small command cluster.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/color_commit_config_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the small command cluster.

## Scenarios

### Claude full color commit config commands

#### should expose clear color and config descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ClearCommandDescriptor.new().aliases.len()).to_equal(2)
expect(ColorCommandDescriptor.new().argumentHint).to_equal("<color|default>")
expect(ConfigCommandDescriptor.new().aliases[0]).to_equal("settings")
expect(callConfigCommand().defaultTab).to_equal("Config")
```

</details>

#### should model color command decisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = ColorCommandState.new(false, "sid", "/transcript", "agent", "")
expect(callColorCommand("", state, ["red", "blue"]).message).to_contain("Please provide")
expect(callColorCommand("red", state, ["red", "blue"]).state.currentColor).to_equal("red")
expect(callColorCommand("default", state, ["red"]).savedColor).to_equal("default")
expect(callColorCommand("green", state, ["red"]).message).to_contain("Invalid color")
expect(callColorCommand("red", ColorCommandState.new(true, "sid", "p", "", ""), ["red"]).message).to_contain("swarm teammate")
```

</details>

#### should model commit prompts and allowed tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(commitCommandDescriptor().name).to_equal("commit")
expect(commitAllowedTools().len()).to_equal(3)
expect(commitPromptContent("ant", true, "undercover", "attr")).to_contain("undercover")
expect(commitPromptContent("", false, "", "attr")).to_contain("Git Safety Protocol")
expect(commitPushPrCommandDescriptor("main").name).to_equal("commit-push-pr")
expect(commitPushPrAllowedTools().len()).to_be_greater_than(10)
expect(commitPushPrPromptContent("main", "prattr", "", "safe", "user", "", false, "", "extra")).to_contain("Additional instructions")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clearIndexSourceLinesModeled()).to_equal(19)
expect(colorCommandSourceLinesModeled()).to_equal(93)
expect(colorIndexSourceLinesModeled()).to_equal(16)
expect(commitSourceLinesModeled()).to_equal(92)
expect(commitPushPrSourceLinesModeled()).to_equal(158)
expect(configCommandSourceLinesModeled()).to_equal(6)
expect(configIndexSourceLinesModeled()).to_equal(11)
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
