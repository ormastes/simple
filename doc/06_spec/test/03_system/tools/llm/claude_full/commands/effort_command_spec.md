# Claude Full Effort Command

> Mirrors `tmp/claude/claude-code-main/src/commands/effort` command metadata,

<!-- sdn-diagram:id=effort_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=effort_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

effort_command_spec -> std
effort_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=effort_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Effort Command

Mirrors `tmp/claude/claude-code-main/src/commands/effort` command metadata,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/effort_command_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/effort` command metadata,
argument handling, current-status rendering, and env override messages.

## Scenarios

### Claude full effort command

#### matches command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = effortCommand(true)

expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("effort")
expect(command.description).to_equal("Set effort level for model usage")
expect(command.argumentHint).to_equal("[low|medium|high|max|auto]")
expect(command.immediate).to_equal(true)
expect(command.loadPath).to_equal("./effort.js")
expect(effortIndexSourceLinesModeled()).to_equal(13)
```

</details>

#### renders help and current effort states

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help = callEffort("--help", "", "claude-sonnet-4-5", "", "")
expect(help.rendered).to_equal("done")
expect(help.message).to_contain("Usage: /effort [low|medium|high|max|auto]")
expect(help.message).to_contain("- max: Maximum capability with deepest reasoning (Opus 4.6 only)")

val autoState = callEffort("", "", "claude-sonnet-4-5", "", "")
expect(autoState.rendered).to_equal("show-current")
expect(autoState.message).to_equal("Effort level: auto (currently medium)")

val current = callEffort("status", "high", "claude-sonnet-4-5", "", "")
expect(current.message).to_equal("Current effort level: high (Comprehensive implementation with extensive testing)")

val envAuto = callEffort("current", "high", "claude-opus-4-6", "auto", "")
expect(envAuto.message).to_equal("Effort level: auto (currently high)")
```

</details>

#### sets persistable and session-only effort values

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val low = callEffort("LOW", "", "claude-sonnet-4-5", "", "")
expect(low.rendered).to_equal("apply-and-close")
expect(low.message).to_equal("Set effort level to low: Quick, straightforward implementation")
expect(low.hasEffortUpdate).to_equal(true)
expect(low.effortValue).to_equal("low")
expect(low.settingsValue).to_equal("low")
expect(low.loggedEffort).to_equal("low")

val max = callEffort("max", "", "claude-opus-4-6", "", "")
expect(max.message).to_equal("Set effort level to max (this session only): Maximum capability with deepest reasoning (Opus 4.6 only)")
expect(max.hasEffortUpdate).to_equal(true)
expect(max.effortValue).to_equal("max")
expect(max.settingsValue).to_equal("")
```

</details>

#### clears effort and reports invalid arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unset = callEffort("unset", "high", "claude-sonnet-4-5", "", "")
expect(unset.message).to_equal("Effort level set to auto")
expect(unset.hasEffortUpdate).to_equal(true)
expect(unset.effortValue).to_equal("")
expect(unset.loggedEffort).to_equal("auto")

val invalid = callEffort("turbo", "", "claude-sonnet-4-5", "", "")
expect(invalid.message).to_equal("Invalid argument: turbo. Valid options are: low, medium, high, max, auto")
expect(invalid.hasEffortUpdate).to_equal(false)
```

</details>

#### models settings errors and env override warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val failure = callEffort("high", "", "claude-sonnet-4-5", "", "disk denied")
expect(failure.message).to_equal("Failed to set effort level: disk denied")
expect(failure.hasEffortUpdate).to_equal(false)

val overridden = callEffort("medium", "", "claude-sonnet-4-5", "high", "")
expect(overridden.message).to_equal("CLAUDE_CODE_EFFORT_LEVEL=high overrides this session - clear it and medium takes over")
expect(overridden.hasEffortUpdate).to_equal(true)
expect(overridden.effortValue).to_equal("medium")
expect(overridden.settingsValue).to_equal("medium")

val sessionOnly = callEffort("max", "", "claude-opus-4-6", "high", "")
expect(sessionOnly.message).to_equal("Not applied: CLAUDE_CODE_EFFORT_LEVEL=high overrides effort this session, and max is session-only (nothing saved)")
expect(sessionOnly.effortValue).to_equal("max")

val cleared = callEffort("auto", "high", "claude-sonnet-4-5", "medium", "")
expect(cleared.message).to_equal("Cleared effort from settings, but CLAUDE_CODE_EFFORT_LEVEL=medium still controls this session")
expect(cleared.hasEffortUpdate).to_equal(true)
expect(cleared.effortValue).to_equal("")

expect(effortSourceLinesModeled()).to_equal(182)
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
