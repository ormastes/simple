# Claude Full AgentsList Component

> Checks the modeled list filtering, sorting, selection, empty state, and source helpers.

<!-- sdn-diagram:id=agents_list_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agents_list_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agents_list_spec -> std
agents_list_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agents_list_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full AgentsList Component

Checks the modeled list filtering, sorting, selection, empty state, and source helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/agents_list_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the modeled list filtering, sorting, selection, empty state, and source helpers.

## Scenarios

### Claude full AgentsList component

#### filters by query and source

- Search matches description, source filter narrows visible rows
   - Expected: visible.len() equals `1`
   - Expected: visible[0].id equals `agent-qa`
   - Expected: filterAgents(items, "sonnet", "all").len() equals `2`
   - Expected: filterAgents(items, "Write", "builtin")[0].name equals `Docs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Search matches description, source filter narrows visible rows")
val items = sampleAgentsListItems()
val state = AgentsListState.new("test plans", "user", "")
val visible = visibleAgents(items, state)
expect(visible.len()).to_equal(1)
expect(visible[0].id).to_equal("agent-qa")
expect(filterAgents(items, "sonnet", "all").len()).to_equal(2)
expect(filterAgents(items, "Write", "builtin")[0].name).to_equal("Docs")
```

</details>

#### sorts by name and keeps selection stable

- Unsorted input renders alphabetically and selection moves with wrapping
- AgentListItem new
- AgentListItem new
- AgentListItem new
   - Expected: sorted[0].id equals `a`
   - Expected: sorted[1].id equals `m`
   - Expected: sorted[2].id equals `z`
   - Expected: selectNextAgent(items, selected).selectedId equals `z`
   - Expected: selectPreviousAgent(items, selected).selectedId equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Unsorted input renders alphabetically and selection moves with wrapping")
val items = [
    AgentListItem.new("z", "Zeta", "last", "project", "sonnet", "ready", [], false, true),
    AgentListItem.new("a", "Alpha", "first", "user", "haiku", "idle", [], false, true),
    AgentListItem.new("m", "Middle", "middle", "builtin", "sonnet", "ready", [], false, true)
]
val sorted = sortAgentsByName(items)
expect(sorted[0].id).to_equal("a")
expect(sorted[1].id).to_equal("m")
expect(sorted[2].id).to_equal("z")
val selected = AgentsListState.new("", "all", "m")
expect(selectNextAgent(items, selected).selectedId).to_equal("z")
expect(selectPreviousAgent(items, selected).selectedId).to_equal("a")
expect(findAgentById(items, "missing")).to_be_nil()
```

</details>

#### renders selected rows and summaries

- Render includes header counts, selected marker, source label, and summary parts


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render includes header counts, selected marker, source label, and summary parts")
val items = sampleAgentsListItems()
val state = AgentsListState.new("", "all", "agent-review")
val output = renderAgentsList(items, state)
expect(output).to_contain("Agents 3/3")
expect(output).to_contain("> Review [Project] ready")
expect(output).to_contain("model sonnet")
expect(output).to_contain("tools Read,Grep")
expect(output).to_contain("default")
expect(renderAgentSummary(items[1])).to_contain("status idle")
```

</details>

#### normalizes empty state and model selection

- No matches explain the active filters; models clamp selection to first visible row
   - Expected: renderAgentsEmptyState(AgentsListState.new("", "all", "")) equals `agentsListEmptyMessage()`
   - Expected: model.state.selectedId equals `agent-docs`
   - Expected: model.selectedItem().? is true
   - Expected: selected.name equals `Docs`
   - Expected: createAgentsList([]).render() equals `agentsListEmptyMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("No matches explain the active filters; models clamp selection to first visible row")
val items = sampleAgentsListItems()
val emptyState = AgentsListState.new("missing", "project", "")
expect(renderAgentsEmptyState(AgentsListState.new("", "all", ""))).to_equal(agentsListEmptyMessage())
expect(renderAgentsList(items, emptyState)).to_contain("No agents match search \"missing\" and source Project")
val model = AgentsListModel.new(items, AgentsListState.new("docs", "builtin", "agent-review"))
expect(model.state.selectedId).to_equal("agent-docs")
expect(model.selectedItem().?).to_equal(true)
if val Some(selected) = model.selectedItem():
    expect(selected.name).to_equal("Docs")
expect(createAgentsList([]).render()).to_equal(agentsListEmptyMessage())
```

</details>

#### exports source helper parity

- Source labels and upstream helper names are stable
   - Expected: sourceDisplayName("built-in") equals `Built-in`
   - Expected: sourceBadge("project") equals `[Project]`
   - Expected: agentsListModeledSourceFile() equals `src/components/agents/AgentsList.tsx`
   - Expected: agentsListModeledSourceHelper() equals `getAgentDefinitionsWithOverrides`
   - Expected: agentsListModeledSelectionHelper() equals `useListSelection`
   - Expected: agentsListModeledFilterHelper() equals `filterAgents`
   - Expected: agentsListModeledSortHelper() equals `sortAgentsByName`
   - Expected: agentsListSourceLinesModeled() equals `439`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Source labels and upstream helper names are stable")
expect(sourceDisplayName("built-in")).to_equal("Built-in")
expect(sourceBadge("project")).to_equal("[Project]")
expect(sourceOptions()).to_contain("all")
expect(sourceOptions()).to_contain("project")
expect(sourceOptions()).to_contain("user")
expect(sourceOptions()).to_contain("builtin")
expect(agentsListModeledSourceFile()).to_equal("src/components/agents/AgentsList.tsx")
expect(agentsListModeledSourceHelper()).to_equal("getAgentDefinitionsWithOverrides")
expect(agentsListModeledSelectionHelper()).to_equal("useListSelection")
expect(agentsListModeledFilterHelper()).to_equal("filterAgents")
expect(agentsListModeledSortHelper()).to_equal("sortAgentsByName")
expect(agentsListSourceLinesModeled()).to_equal(439)
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
