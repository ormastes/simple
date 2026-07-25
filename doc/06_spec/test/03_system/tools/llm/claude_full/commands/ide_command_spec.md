# Claude Full IDE Command

> Mirrors `tmp/claude/claude-code-main/src/commands/ide` metadata, IDE

<!-- sdn-diagram:id=ide_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_command_spec -> std
ide_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full IDE Command

Mirrors `tmp/claude/claude-code-main/src/commands/ide` metadata, IDE

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/ide_command_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/ide` metadata, IDE
selection, open/install routing, MCP dynamic config behavior, and workspace
formatting for the IDE-only Claude-full parity slice.

## Scenarios

### Claude full ide command

#### matches command metadata and source line parity

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = ideCommand()
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("ide")
expect(command.description).to_equal("Manage IDE integrations and show status")
expect(command.argumentHint).to_equal("[open]")
expect(command.loadPath).to_equal("./ide.js")
expect(ideIndexSourceLinesModeled()).to_equal(11)
expect(ideSourceLinesModeled()).to_equal(645)
expect(ideConnectionTimeoutMs()).to_equal(35000)
expect(ideCommandEventName()).to_equal("tengu_ext_ide_command")
```

</details>

#### formats workspace folders like upstream

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val folders = ["/repo/app/frontend", "/repo/packages/backend-service-with-a-very-long-name", "/repo/tools/extra"]
val formatted = formatWorkspaceFoldersWithCwd(folders, 34, "/repo", "/")
expect(formatted).to_contain("app/frontend")
expect(formatted).to_contain("…")
expect(formatted).to_end_with(", …")
expect(formatWorkspaceFoldersWithCwd([], 100, "/repo", "/")).to_equal("")
```

</details>

#### renders IDE screen options, warnings, tips, and unavailable IDEs

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = IdeInfo.new("VS Code", 3001, "http://localhost:3001", true, ["/repo/a"], "tok1", false)
val second = IdeInfo.new("VS Code", 3002, "ws://localhost:3002", true, ["/repo/b"], "tok2", true)
val invalid = IdeInfo.new("PyCharm", 4001, "http://localhost:4001", false, ["/other/project"], "", false)
val screen = renderIdeScreen([first, second], [invalid], first, false, false, "/repo")
expect(screen.title).to_equal("Select IDE")
expect(screen.subtitle).to_equal("Connect to an IDE for integrated development features.")
expect(screen.color).to_equal("ide")
expect(screen.options.len()).to_equal(3)
expect(screen.options[0].description).to_equal("a")
expect(screen.options[2].label).to_equal("None")
expect(screen.body).to_contain("Only one Claude Code instance can be connected to VS Code")
expect(screen.body).to_contain("Tip: You can enable auto-connect to IDE")
expect(screen.body).to_contain("Found 1 other running IDE(s)")
expect(screen.body).to_contain("PyCharm: /other/project")

val emptyJetBrains = renderIdeScreen([], [], IdeInfo.new("", 0, "", false, [], "", false), true, true, "/repo")
expect(emptyJetBrains.body).to_contain("https://docs.claude.com/s/claude-code-jetbrains")
```

</details>

#### finds current IDE only from dynamic sse/ws config

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ide = IdeInfo.new("Cursor", 3100, "ws://localhost:3100", true, [], "auth", true)
val current = findCurrentIDE([ide], IdeDynamicConfig.forIde(ide))
expect(current.name).to_equal("Cursor")
expect(current.port).to_equal(3100)
expect(IdeDynamicConfig.forIde(ide).typeName).to_equal("ws-ide")
expect(findCurrentIDE([ide], IdeDynamicConfig.none()).name).to_equal("")
expect(findCurrentIDE([ide], IdeDynamicConfig(typeName: "stdio", url: ide.url, ideName: ide.name, authToken: "", ideRunningInWindows: false, scope: "")).name).to_equal("")
```

</details>

#### routes open command and selected IDE open results

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vscode = IdeInfo.new("Visual Studio Code", 3001, "http://localhost:3001", true, [], "", false)
val pycharm = IdeInfo.new("PyCharm", 3002, "http://localhost:3002", true, [], "", false)
val invalid = IdeInfo.new("Broken", 1, "", false, [], "", false)
val selector = callIdeOpen([invalid, vscode], "/repo", false)
expect(selector.rendered).to_equal("open-selector")
expect(selector.selectedName).to_equal("Visual Studio Code")
expect(selector.openedPath).to_equal("/repo")

expect(callIdeOpen([invalid], "/repo", false).doneMessage).to_equal("No IDEs with Claude Code extension detected.")
expect(openSelectedIDE(vscode, "/repo", false, 0, false).doneMessage).to_equal("Opened project in Visual Studio Code")
expect(openSelectedIDE(vscode, "/repo/wt", true, 1, false).doneMessage).to_equal("Failed to open in Visual Studio Code. Try opening manually: /repo/wt")
expect(openSelectedIDE(pycharm, "/repo", false, 0, true).doneMessage).to_equal("Please open the project manually in PyCharm: /repo")
```

</details>

#### models install extension routing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(installIDEMessage("intellij")).to_contain("Installed plugin to IntelliJ IDEA")
expect(installIDEMessage("intellij")).to_contain("restart your IDE")
expect(installIDEMessage("cursor")).to_equal("Installed extension to Cursor")
expect(selectRunningIDEForInstall("pycharm").doneMessage).to_contain("Installed plugin to PyCharm")

val multiple = callIde("", [], ["vscode", "cursor"], IdeDynamicConfig.none(), true, false, "/repo", false)
expect(multiple.rendered).to_equal("running-selector")

val single = callIde("", [], ["cursor"], IdeDynamicConfig.none(), true, false, "/repo", false)
expect(single.rendered).to_equal("install-on-mount")
expect(single.installIDE).to_equal("cursor")
expect(single.doneMessage).to_equal("Installed extension to Cursor")
```

</details>

#### connects, disconnects, and reports connection status

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val oldIde = IdeInfo.new("VS Code", 3001, "http://localhost:3001", true, [], "old", false)
val newIde = IdeInfo.new("Cursor", 3002, "ws://localhost:3002", true, [], "new", true)
val missingChanger = connectSelectedIDE(newIde, oldIde, false)
expect(missingChanger.doneMessage).to_equal("Error connecting to IDE.")

val disconnected = connectSelectedIDE(IdeInfo.new("", 0, "", false, [], "", false), oldIde, true)
expect(disconnected.doneMessage).to_equal("Disconnected from VS Code.")
expect(disconnected.cacheCleared).to_equal(true)
expect(disconnected.toolsRemoved).to_equal(true)
expect(disconnected.commandsRemoved).to_equal(true)

val connecting = connectSelectedIDE(newIde, oldIde, true)
expect(connecting.rendered).to_equal("connecting")
expect(connecting.config.typeName).to_equal("ws-ide")
expect(connecting.config.ideName).to_equal("Cursor")
expect(connecting.config.authToken).to_equal("new")
expect(connecting.config.ideRunningInWindows).to_equal(true)
expect(connecting.config.scope).to_equal("dynamic")

expect(connectionStatusMessage(newIde, "connected")).to_equal("Connected to Cursor.")
expect(connectionStatusMessage(newIde, "failed")).to_equal("Failed to connect to Cursor.")
expect(connectionStatusMessage(newIde, "timeout")).to_equal("Connection to Cursor timed out.")
expect(connectionStatusMessage(newIde, "pending")).to_equal("")
```

</details>

#### routes top-level call between open, install, and normal flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ide = IdeInfo.new("VS Code", 3001, "http://localhost:3001", true, [], "", false)
expect(callIde(" open ", [ide], [], IdeDynamicConfig.none(), false, true, "/repo", false).rendered).to_equal("open-selector")

val config = IdeDynamicConfig.forIde(ide)
val normal = callIde("", [ide], [], config, true, false, "/repo", false)
expect(normal.rendered).to_equal("flow:Select IDE")
expect(normal.selectedName).to_equal("VS Code")
expect(normal.config.url).to_equal("http://localhost:3001")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
