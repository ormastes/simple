# Claude Full Terminal Setup Command

> Checks terminalSetup command parity with modern SSpec coverage.

<!-- sdn-diagram:id=terminal_setup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal_setup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal_setup_spec -> std
terminal_setup_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal_setup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Terminal Setup Command

Checks terminalSetup command parity with modern SSpec coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/terminal_setup_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks terminalSetup command parity with modern SSpec coverage.

## Scenarios

### Claude full terminalSetup command

#### exposes command metadata

- Load terminalSetup command metadata
- Assert command name and local JSX load path
   - Expected: command.typeName equals `local-jsx`
   - Expected: command.name equals `terminal-setup`
   - Expected: command.description equals `Install Claude Code terminal integration`
   - Expected: command.argumentHint equals ``
   - Expected: command.loadPath equals `./terminalSetup.js`
   - Expected: terminalSetupCommandName() equals `terminal-setup`
   - Expected: terminalSetupCommandDescription() equals `Install Claude Code terminal integration`
   - Expected: terminalSetupLoadPath() equals `./terminalSetup.js`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load terminalSetup command metadata")
val command = terminalSetupCommand()

step("Assert command name and local JSX load path")
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("terminal-setup")
expect(command.description).to_equal("Install Claude Code terminal integration")
expect(command.argumentHint).to_equal("")
expect(command.loadPath).to_equal("./terminalSetup.js")
expect(terminalSetupCommandName()).to_equal("terminal-setup")
expect(terminalSetupCommandDescription()).to_equal("Install Claude Code terminal integration")
expect(terminalSetupLoadPath()).to_equal("./terminalSetup.js")
```

</details>

#### models platform scripts and shell snippets

- Normalize Claude terminal setup platforms
   - Expected: terminalSetupNormalizedPlatform("macos") equals `darwin`
   - Expected: terminalSetupNormalizedPlatform("win32") equals `windows`
   - Expected: terminalSetupNormalizedPlatform("linux") equals `linux`
- Render shell profile snippets
   - Expected: terminalSetupShellSnippet("zsh") equals `export CLAUDE_CODE_TERMINAL_SETUP=1`
   - Expected: terminalSetupShellSnippet("fish") equals `set -gx CLAUDE_CODE_TERMINAL_SETUP 1`
   - Expected: terminalSetupShellSnippet("powershell") equals `$env:CLAUDE_CODE_TERMINAL_SETUP = '1'`
- Render platform-specific scripts


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Normalize Claude terminal setup platforms")
expect(terminalSetupNormalizedPlatform("macos")).to_equal("darwin")
expect(terminalSetupNormalizedPlatform("win32")).to_equal("windows")
expect(terminalSetupNormalizedPlatform("linux")).to_equal("linux")

step("Render shell profile snippets")
expect(terminalSetupShellSnippet("zsh")).to_equal("export CLAUDE_CODE_TERMINAL_SETUP=1")
expect(terminalSetupShellSnippet("fish")).to_equal("set -gx CLAUDE_CODE_TERMINAL_SETUP 1")
expect(terminalSetupShellSnippet("powershell")).to_equal("$env:CLAUDE_CODE_TERMINAL_SETUP = '1'")

step("Render platform-specific scripts")
expect(terminalSetupScriptFor("darwin", "zsh")).to_contain("claude terminal-setup --platform darwin --shell zsh")
expect(terminalSetupScriptFor("linux", "bash")).to_contain("claude terminal-setup --platform linux --shell bash")
expect(terminalSetupScriptFor("windows", "powershell")).to_contain("claude.exe terminal-setup --shell powershell")
```

</details>

#### models shell profile paths

- Map shells to profile files
   - Expected: terminalSetupProfilePath("zsh") equals `~/.zshrc`
   - Expected: terminalSetupProfilePath("bash") equals `~/.bashrc`
   - Expected: terminalSetupProfilePath("fish") equals `~/.config/fish/config.fish`
   - Expected: terminalSetupProfilePath("powershell") equals `$PROFILE`
   - Expected: terminalSetupProfilePath("unknown") equals `~/.profile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Map shells to profile files")
expect(terminalSetupProfilePath("zsh")).to_equal("~/.zshrc")
expect(terminalSetupProfilePath("bash")).to_equal("~/.bashrc")
expect(terminalSetupProfilePath("fish")).to_equal("~/.config/fish/config.fish")
expect(terminalSetupProfilePath("powershell")).to_equal("$PROFILE")
expect(terminalSetupProfilePath("unknown")).to_equal("~/.profile")
```

</details>

#### reports status and summary for setup outcomes

- Check ready setup
   - Expected: terminalSetupStatus(ready) equals `ready`
   - Expected: callTerminalSetup(ready).ok is true
- Check configured, create-profile, and blocked states
   - Expected: callTerminalSetup(configured).status equals `already-configured`
   - Expected: callTerminalSetup(createProfile).status equals `create-profile`
   - Expected: callTerminalSetup(createProfile).profilePath equals `~/.config/fish/config.fish`
   - Expected: callTerminalSetup(blocked).ok is false
   - Expected: callTerminalSetup(blocked).status equals `blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check ready setup")
val ready = TerminalSetupState.new("linux", "bash", "", true, false, true)
expect(terminalSetupStatus(ready)).to_equal("ready")
expect(terminalSetupSummary(ready)).to_contain("~/.bashrc")
expect(callTerminalSetup(ready).ok).to_equal(true)
expect(callTerminalSetup(ready).summary).to_contain("Add Claude terminal integration")

step("Check configured, create-profile, and blocked states")
val configured = TerminalSetupState.new("darwin", "zsh", "", true, true, true)
expect(callTerminalSetup(configured).status).to_equal("already-configured")
expect(callTerminalSetup(configured).summary).to_contain("already configured")

val createProfile = TerminalSetupState.new("linux", "fish", "", false, false, true)
expect(callTerminalSetup(createProfile).status).to_equal("create-profile")
expect(callTerminalSetup(createProfile).profilePath).to_equal("~/.config/fish/config.fish")

val blocked = TerminalSetupState.new("windows", "powershell", "$PROFILE.CurrentUserCurrentHost", true, false, false)
expect(callTerminalSetup(blocked).ok).to_equal(false)
expect(callTerminalSetup(blocked).status).to_equal("blocked")
expect(callTerminalSetup(blocked).summary).to_contain("update it manually")
```

</details>

#### keeps source floors visible

- Check modeled source line floors


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check modeled source line floors")
expect(terminalSetupIndexSourceLinesModeled()).to_be_greater_than(22)
expect(terminalSetupSourceLinesModeled()).to_be_greater_than(529)
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
