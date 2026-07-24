# Claude Full Root Commands Registry

> Checks modern SSpec parity for the top-level slash command registry.

<!-- sdn-diagram:id=root_commands_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=root_commands_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

root_commands_registry_spec -> std
root_commands_registry_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=root_commands_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Root Commands Registry

Checks modern SSpec parity for the top-level slash command registry.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/root_commands_registry_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the top-level slash command registry.

## Scenarios

### Claude full root commands registry

#### contains known top-level commands

- Build the modeled registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the modeled registry")
val names = rootCommandNames()
expect(names).to_contain("help")
expect(names).to_contain("clear")
expect(names).to_contain("config")
expect(names).to_contain("mcp")
expect(names).to_contain("agents")
```

</details>

#### resolves slash names and aliases

- Resolve direct slash names
   - Expected: help.found is true
   - Expected: help.command.name equals `help`
   - Expected: help.matchedAlias equals ``
- Resolve aliases without slash prefixes
   - Expected: reset.found is true
   - Expected: reset.command.name equals `clear`
   - Expected: reset.matchedAlias equals `reset`
- Report missing commands explicitly
   - Expected: findRootCommand("/missing").found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve direct slash names")
val help = findRootCommand("/help")
expect(help.found).to_equal(true)
expect(help.command.name).to_equal("help")
expect(help.matchedAlias).to_equal("")

step("Resolve aliases without slash prefixes")
val reset = findRootCommand("reset")
expect(reset.found).to_equal(true)
expect(reset.command.name).to_equal("clear")
expect(reset.matchedAlias).to_equal("reset")

step("Report missing commands explicitly")
expect(findRootCommand("/missing").found).to_equal(false)
```

</details>

#### models disabled and hidden command behavior

- Hidden commands resolve but are excluded from visible summaries
   - Expected: debug.found is true
   - Expected: debug.command.hidden is true
   - Expected: hidden admission is false by default and true with the fixture
- Disabled commands resolve with disabled state
   - Expected: remote.found is true
   - Expected: remote.command.enabled is false
   - Expected: disabled admission remains false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Hidden commands resolve but are excluded from visible summaries")
val debug = findRootCommand("/debug-tool-call")
expect(debug.found).to_equal(true)
expect(debug.command.hidden).to_equal(true)
expect(admitRootCommand("/debug-tool-call", false).found).to_equal(false)
expect(admitRootCommand("/debug-tool-call", true).found).to_equal(true)
expect(visibleRootCommandSummary()).to_contain("/help core")
expect(visibleRootCommandSummary()).to_contain("/mcp integrations")

step("Disabled commands resolve with disabled state")
val remote = findRootCommand("/remote-setup")
expect(remote.found).to_equal(true)
expect(remote.command.enabled).to_equal(false)
expect(admitRootCommand("/remote-setup", true).found).to_equal(false)
```

</details>

#### filters by category and exposes source lines

- Filter commands by category
   - Expected: core.len() equals `3`
   - Expected: core[0].name equals `help`
- Expose stable source line helpers
   - Expected: rootCommandSourceLine("/help") equals `1`
   - Expected: rootCommandSourceLine("reset") equals `1`
   - Expected: rootCommandSourceLine("/missing") equals `0`
   - Expected: rootCommandsSourceLinesModeled() equals `754`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Filter commands by category")
val core = rootCommandsByCategory("core")
expect(core.len()).to_equal(3)
expect(core[0].name).to_equal("help")

step("Expose stable source line helpers")
expect(rootCommandSourceLine("/help")).to_equal(1)
expect(rootCommandSourceLine("reset")).to_equal(1)
expect(rootCommandSourceLine("/missing")).to_equal(0)
expect(rootCommandsSourceLinesModeled()).to_equal(754)
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
