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
| 5 | 5 | 0 | 0 |

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
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the top-level slash command registry.

## Scenarios

### Claude full root commands registry

#### should contain known top-level commands

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

#### should resolve slash names and aliases

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
expect(help.found).to_be(true)
expect(help.command.name).to_equal("help")
expect(help.matchedAlias).to_equal("")

step("Resolve aliases without slash prefixes")
val reset = findRootCommand("reset")
expect(reset.found).to_be(true)
expect(reset.command.name).to_equal("clear")
expect(reset.matchedAlias).to_equal("reset")

step("Report missing commands explicitly")
expect(findRootCommand("/missing").found).to_be(false)
```

</details>

#### should derive lookup admission and visibility for every registry record

- Derive lookup identities from each registry record
   - Expected: canonical and slash lookup forms identify the same registry record
- Resolve every alias to the same canonical record
   - Expected: every alias reports its canonical command and matched alias
- Compare admission and visibility with record flags
   - Expected: default admission and visible membership equal `enabled and not hidden`
   - Expected: hidden-feature admission equals `enabled`
- Require hidden and disabled registry coverage
   - Expected: hiddenCount is greater than `0`
   - Expected: disabledCount is greater than `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive lookup identities from each registry record")
val registry = rootCommandRegistry()
val visible = visibleRootCommands()
var hiddenCount = 0
var disabledCount = 0
for command in registry:
    val canonical = findRootCommand(command.name)
    expect(canonical.found).to_be(true)
    expect(canonical.command.name).to_equal(command.name)
    expect(canonical.command.slashName).to_equal(command.slashName)
    expect(canonical.matchedAlias).to_equal("")

    val slash = findRootCommand(command.slashName)
    expect(slash.found).to_be(true)
    expect(slash.command.name).to_equal(canonical.command.name)
    expect(slash.command.slashName).to_equal(canonical.command.slashName)
    expect(slash.matchedAlias).to_equal("")

    step("Resolve every alias to the same canonical record")
    for alias in command.aliases:
        val aliasLookup = findRootCommand(alias)
        expect(aliasLookup.found).to_be(true)
        expect(aliasLookup.command.name).to_equal(canonical.command.name)
        expect(aliasLookup.command.slashName).to_equal(canonical.command.slashName)
        expect(aliasLookup.matchedAlias).to_equal(alias)

    step("Compare admission and visibility with record flags")
    val expectedDefaultAdmission = command.enabled and not command.hidden
    expect(admitRootCommand(command.name, false).found).to_equal(expectedDefaultAdmission)
    expect(admitRootCommand(command.name, true).found).to_equal(command.enabled)
    var isVisible = false
    for visibleCommand in visible:
        if visibleCommand.name == command.name:
            isVisible = true
    expect(isVisible).to_equal(expectedDefaultAdmission)

    if command.hidden:
        hiddenCount = hiddenCount + 1
    if not command.enabled:
        disabledCount = disabledCount + 1

step("Require hidden and disabled registry coverage")
expect(hiddenCount).to_be_greater_than(0)
expect(disabledCount).to_be_greater_than(0)
```

</details>

#### should model disabled and hidden command behavior

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
expect(debug.found).to_be(true)
expect(debug.command.hidden).to_be(true)
expect(admitRootCommand("/debug-tool-call", false).found).to_be(false)
expect(admitRootCommand("/debug-tool-call", true).found).to_be(true)
expect(visibleRootCommandSummary()).to_contain("/help core")
expect(visibleRootCommandSummary()).to_contain("/mcp integrations")

step("Disabled commands resolve with disabled state")
val remote = findRootCommand("/remote-setup")
expect(remote.found).to_be(true)
expect(remote.command.enabled).to_be(false)
expect(admitRootCommand("/remote-setup", true).found).to_be(false)
```

</details>

#### should filter by category and expose source lines

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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
