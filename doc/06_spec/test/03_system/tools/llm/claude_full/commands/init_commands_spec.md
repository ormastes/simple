# Claude Full Init Commands

> Mirrors `tmp/claude/claude-code-main/src/commands/init.ts` and

<!-- sdn-diagram:id=init_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=init_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

init_commands_spec -> std
init_commands_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=init_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Init Commands

Mirrors `tmp/claude/claude-code-main/src/commands/init.ts` and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/init_commands_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/init.ts` and
`tmp/claude/claude-code-main/src/commands/init-verifiers.ts` for command
metadata, feature-gated prompt selection, and verifier-skill prompt contracts.

## Scenarios

### Claude full init commands

#### matches /init metadata and feature-gated descriptions

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val oldCommand = initCommand(false, "ant", "true")
expect(oldCommand.typeName).to_equal("prompt")
expect(oldCommand.name).to_equal("init")
expect(oldCommand.description).to_equal("Initialize a new CLAUDE.md file with codebase documentation")
expect(oldCommand.contentLength).to_equal(0)
expect(oldCommand.progressMessage).to_equal("analyzing your codebase")
expect(oldCommand.source).to_equal("builtin")

val newForAnt = initCommand(true, "ant", "")
expect(newForAnt.description).to_equal("Initialize new CLAUDE.md file(s) and optional skills/hooks with codebase documentation")
val newForEnv = initCommand(true, "external", "yes")
expect(newForEnv.description).to_equal("Initialize new CLAUDE.md file(s) and optional skills/hooks with codebase documentation")
val oldForExternal = initCommand(true, "external", "no")
expect(oldForExternal.description).to_equal("Initialize a new CLAUDE.md file with codebase documentation")
```

</details>

#### models NEW_INIT and environment truthiness exactly enough for prompt routing

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(isInitEnvTruthy("1")).to_equal(true)
expect(isInitEnvTruthy(" TRUE ")).to_equal(true)
expect(isInitEnvTruthy("yes")).to_equal(true)
expect(isInitEnvTruthy("on")).to_equal(true)
expect(isInitEnvTruthy("0")).to_equal(false)
expect(isInitEnvTruthy("false")).to_equal(false)
expect(useNewInitPrompt(true, "ant", "")).to_equal(true)
expect(useNewInitPrompt(true, "user", "true")).to_equal(true)
expect(useNewInitPrompt(true, "user", "")).to_equal(false)
expect(useNewInitPrompt(false, "ant", "true")).to_equal(false)
```

</details>

#### returns the old init prompt when the new init gate is closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prompt = initPromptText(false, "ant", "true")
expect(prompt).to_contain("Please analyze this codebase and create a CLAUDE.md file")
expect(prompt).to_contain("Commands that will be commonly used")
expect(prompt).to_contain("High-level code architecture and structure")
expect(prompt).to_contain("If there are Cursor rules")
expect(prompt).to_contain("This file provides guidance to Claude Code")
expect(prompt.contains("Also set up skills and hooks?")).to_equal(false)

val parts = getPromptForInitCommand(false, "ant", "true")
expect(parts.len()).to_equal(1)
expect(parts[0].typeName).to_equal("text")
expect(parts[0].textValue).to_equal(prompt)
```

</details>

#### returns the new init prompt when the new init gate is open

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prompt = initPromptText(true, "ant", "")
expect(prompt).to_contain("Set up a minimal CLAUDE.md")
expect(prompt).to_contain("Which CLAUDE.md files should /init set up?")
expect(prompt).to_contain("Also set up skills and hooks?")
expect(prompt).to_contain("Launch a subagent to survey the codebase")
expect(prompt).to_contain("Show the proposal via AskUserQuestion's preview field")
expect(prompt).to_contain("Write a minimal CLAUDE.local.md")
expect(prompt).to_contain("Create each skill at .claude/skills/<skill-name>/SKILL.md")
expect(prompt).to_contain("load the hook reference with the update-config skill")
expect(initSourceLinesModeled()).to_equal(256)
```

</details>

#### matches /init-verifiers metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = initVerifiersCommand()
expect(command.typeName).to_equal("prompt")
expect(command.name).to_equal("init-verifiers")
expect(command.description).to_equal("Create verifier skill(s) for automated verification of code changes")
expect(command.contentLength).to_equal(0)
expect(command.progressMessage).to_equal("analyzing your project and creating verifier skills")
expect(command.source).to_equal("builtin")
```

</details>

#### returns verifier prompt content with concrete phases and tool contracts

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prompt = initVerifiersPrompt()
expect(prompt).to_contain("Use the TodoWrite tool")
expect(prompt).to_contain("Do NOT create verifiers for unit tests or typechecking")
expect(prompt).to_contain("web UI (Playwright), CLI (Tmux), and API (HTTP)")
expect(prompt).to_contain("## Phase 1: Auto-Detection")
expect(prompt).to_contain("## Phase 2: Verification Tool Setup")
expect(prompt).to_contain("## Phase 3: Interactive Q&A")
expect(prompt).to_contain("## Phase 4: Generate Verifier Skill")
expect(prompt).to_contain("## Phase 5: Confirm Creation")
expect(prompt).to_contain(".claude/skills/<verifier-name>/SKILL.md")
expect(prompt).to_contain("mcp__playwright__*")
expect(prompt).to_contain("Bash(asciinema:*)")
expect(prompt).to_contain("Bash(curl:*)")
expect(prompt).to_contain("Report PASS or FAIL")

val parts = getPromptForInitVerifiersCommand()
expect(parts.len()).to_equal(1)
expect(parts[0].typeName).to_equal("text")
expect(parts[0].textValue).to_equal(prompt)
expect(initVerifiersSourceLinesModeled()).to_equal(262)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
