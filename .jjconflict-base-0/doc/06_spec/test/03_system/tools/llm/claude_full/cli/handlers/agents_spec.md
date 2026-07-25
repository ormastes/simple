# Claude Full CLI Agents Handler

> Checks agents subcommand formatting and grouping.

<!-- sdn-diagram:id=agents_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agents_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agents_spec -> std
agents_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agents_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI Agents Handler

Checks agents subcommand formatting and grouping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/handlers/agents_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks agents subcommand formatting and grouping.

## Scenarios

### Claude full cli agents handler

#### formats an agent with model and memory

- Agent type is always first, optional model and memory follow
   - Expected: formatAgent(ResolvedAgent.new("alpha", "general", "project", "", "")) equals `general`
   - Expected: formatAgent(ResolvedAgent.new("alpha", "general", "project", "sonnet", "")) equals `"general · sonnet")`
   - Expected: formatAgent(ResolvedAgent.new("alpha", "general", "project", "sonnet", "2MB")) equals `"general · sonnet · 2MB memory")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Agent type is always first, optional model and memory follow")
expect(formatAgent(ResolvedAgent.new("alpha", "general", "project", "", ""))).to_equal("general")
expect(formatAgent(ResolvedAgent.new("alpha", "general", "project", "sonnet", ""))).to_equal("general · sonnet")
expect(formatAgent(ResolvedAgent.new("alpha", "general", "project", "sonnet", "2MB"))).to_equal("general · sonnet · 2MB memory")
```

</details>

#### prints no agents message for empty output

- No groups means no configured agents
   - Expected: agentsHandlerOutput([]) equals `noAgentsMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("No groups means no configured agents")
expect(agentsHandlerOutput([])).to_equal(noAgentsMessage())
```

</details>

#### renders agents in source order

- The Simple parity slice keeps source order to avoid slow class-array sort
- ResolvedAgent new
- ResolvedAgent new
- ResolvedAgent new
   - Expected: filterAgentsBySource(agents, "project").len() equals `3`
   - Expected: sortAgentsByName(agents).len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The Simple parity slice keeps source order to avoid slow class-array sort")
val agents = [
    ResolvedAgent.new("zeta", "z", "project", "", ""),
    ResolvedAgent.new("alpha", "a", "project", "haiku", ""),
    ResolvedAgent.new("user", "u", "user", "", "1MB")
]
val output = agentsHandlerOutput(agents)
expect(output).to_contain(activeAgentsHeader(3))
expect(output).to_contain("  a · haiku")
expect(output).to_contain("  z")
expect(output).to_contain("  u · 1MB memory")
expect(filterAgentsBySource(agents, "project").len()).to_equal(3)
expect(sortAgentsByName(agents).len()).to_equal(3)
```

</details>

#### marks shadowed agents and excludes them from active count

- Shadowed entries show the winning source and do not increment active total
   - Expected: activeAgentCount([shadowed, live]) equals `1`
   - Expected: getOverrideSourceLabel("builtin") equals `Built-in`
   - Expected: shadowedPrefix("project") equals `(shadowed by Project)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Shadowed entries show the winning source and do not increment active total")
val shadowed = ResolvedAgent.new("alpha", "a", "user", "", "").shadowedBy("project")
val live = ResolvedAgent.new("beta", "b", "user", "", "")
val output = agentsHandlerOutput([shadowed, live])
expect(activeAgentCount([shadowed, live])).to_equal(1)
expect(output).to_contain("1 active agents")
expect(output).to_contain("  (shadowed by Project) a")
expect(output).to_contain("  b")
expect(getOverrideSourceLabel("builtin")).to_equal("Built-in")
expect(shadowedPrefix("project")).to_equal("(shadowed by Project)")
```

</details>

#### exports source-backed dependency names

- Pin dynamic handler collaborators
   - Expected: agentSourceGroups().len() equals `3`
   - Expected: modelDisplaySource() equals `resolveAgentModelDisplay`
   - Expected: overrideResolverSource() equals `resolveAgentOverrides`
   - Expected: activeAgentFilterSource() equals `getActiveAgentsFromList`
   - Expected: definitionsLoaderSource() equals `getAgentDefinitionsWithOverrides`
   - Expected: cwdSource() equals `getCwd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin dynamic handler collaborators")
expect(agentSourceGroups().len()).to_equal(3)
expect(modelDisplaySource()).to_equal("resolveAgentModelDisplay")
expect(overrideResolverSource()).to_equal("resolveAgentOverrides")
expect(activeAgentFilterSource()).to_equal("getActiveAgentsFromList")
expect(definitionsLoaderSource()).to_equal("getAgentDefinitionsWithOverrides")
expect(cwdSource()).to_equal("getCwd")
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
