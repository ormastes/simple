# Claude Full Install Command

> Checks modern SSpec parity for commands/install.tsx.

<!-- sdn-diagram:id=install_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=install_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

install_command_spec -> std
install_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=install_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Install Command

Checks modern SSpec parity for commands/install.tsx.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/install_command_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for commands/install.tsx.

## Scenarios

### Claude full install command

#### should expose install command metadata and source size

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = installCommand()
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("install")
expect(command.description).to_equal("Install Claude Code native build")
expect(command.argumentHint).to_equal("[options]")
expect(installSourceLinesModeled()).to_equal(299)
```

</details>

#### should parse force and first non-flag target

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parseInstallArgs(["--force", "--verbose", "stable", "1.0.34"])
expect(parsed.force).to_equal(true)
expect(parsed.target).to_equal("stable")
val defaults = parseInstallArgs(["--dry-run"])
expect(defaults.force).to_equal(false)
expect(defaults.target).to_equal("")
```

</details>

#### should model install paths and setup notes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(getInstallationPath("linux", "/home/me")).to_equal("~/.local/bin/claude")
expect(getInstallationPath("win32", "C:/Users/me")).to_contain("claude.exe")
expect(setupNotes([])).to_equal("")
val notes = setupNotes(["Add ~/.local/bin to PATH", "Restart shell"])
expect(notes).to_contain("Setup notes:")
expect(notes).to_contain("Restart shell")
```

</details>

#### should run success flow with setup and warning messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = InstallScenario.new(true, "stable", "latest", InstallLatestResult.new("1.0.34", true, false), ["Add ~/.local/bin to PATH"], ["removed old npm"], ["removed alias"], "")
val result = runInstallScenario(scenario)
expect(result.finalState).to_equal("success")
expect(result.version).to_equal("1.0.34")
expect(result.channelOrVersion).to_equal("stable")
expect(result.savedChannel).to_equal("stable")
expect(result.analyticsEvent).to_equal("tengu_claude_install_command")
expect(result.hasVersion).to_equal(1)
expect(result.forced).to_equal(1)
expect(result.cleanupAttempted).to_equal(true)
expect(result.shellAliasCleanupAttempted).to_equal(true)
expect(result.checkInstallCalled).to_equal(true)
expect(result.warnings.len()).to_equal(2)
expect(result.renderedState).to_contain("Claude Code successfully installed!")
expect(result.renderedState).to_contain("claude --help")
expect(result.doneMessage).to_equal("Claude Code installation completed successfully")
expect(result.onDoneDelayMs).to_equal(2000)
```

</details>

#### should use settings fallback and current version when install returns no version

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = InstallScenario.new(false, "", "stable", InstallLatestResult.new("", false, false), [], [], [], "")
val result = runInstallScenario(scenario)
expect(result.finalState).to_equal("success")
expect(result.channelOrVersion).to_equal("stable")
expect(result.version).to_equal("current")
expect(result.savedChannel).to_equal("")
expect(result.hasVersion).to_equal(0)
expect(result.forced).to_equal(0)
expect(result.renderedState).to_end_with("Next: Run claude --help to get started")
```

</details>

#### should model lock failure and generic install errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val locked = runInstallScenario(InstallScenario.new(false, "latest", "", InstallLatestResult.new("", false, true), [], [], [], ""))
expect(locked.finalState).to_equal("error")
expect(locked.message).to_contain("another process is currently installing Claude")
expect(locked.doneMessage).to_equal("Claude Code installation failed")
expect(locked.cleanupAttempted).to_equal(false)
expect(locked.onDoneDelayMs).to_equal(3000)

val failed = runInstallScenario(InstallScenario.new(false, "1.0.34", "", InstallLatestResult.new("", false, false), [], [], [], "network failed"))
expect(failed.finalState).to_equal("error")
expect(failed.message).to_equal("network failed")
expect(failed.renderedState).to_contain("Try running with --force")
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
