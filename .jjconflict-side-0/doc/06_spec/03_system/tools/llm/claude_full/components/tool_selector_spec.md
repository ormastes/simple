# Claude Full ToolSelector Component

> Checks modeled available tools, selected tools, toggles, filtering, disabled tools, summaries, and source helpers.

<!-- sdn-diagram:id=tool_selector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tool_selector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tool_selector_spec -> std
tool_selector_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tool_selector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full ToolSelector Component

Checks modeled available tools, selected tools, toggles, filtering, disabled tools, summaries, and source helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/tool_selector_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modeled available tools, selected tools, toggles, filtering, disabled tools, summaries, and source helpers.

## Scenarios

### Claude full ToolSelector component

#### models available and selected tools

- Create a selector and add enabled tools
   - Expected: selector.tools.len() equals `5`
   - Expected: selector.summary() equals `No tools selected`
   - Expected: selected.selectedTools().len() equals `2`
   - Expected: selected.summary() equals `Selected 2 of 5: Bash, Read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a selector and add enabled tools")
val selector = createToolSelector(sampleToolSelectorTools())
expect(selector.tools.len()).to_equal(5)
expect(selector.summary()).to_equal("No tools selected")

val selected = selector.toggle("read").toggle("bash")
expect(selected.selectedTools().len()).to_equal(2)
expect(selected.summary()).to_equal("Selected 2 of 5: Bash, Read")
expect(selected.render()).to_contain("[x] Bash [Project] enabled")
expect(selected.render()).to_contain("[x] Read [Built-in] enabled")
```

</details>

#### toggles enabled tools and blocks disabled tools

- Toggle on, toggle off, and ignore disabled rows
   - Expected: added.state.lastAction equals `add write`
   - Expected: added.selectedTools().len() equals `1`
   - Expected: removed.state.lastAction equals `remove write`
   - Expected: removed.selectedTools().len() equals `0`
   - Expected: blocked.state.lastAction equals `blocked web-fetch`
   - Expected: blocked.selectedTools().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Toggle on, toggle off, and ignore disabled rows")
val selector = createToolSelector(sampleToolSelectorTools())
val added = selector.toggle("write")
expect(added.state.lastAction).to_equal("add write")
expect(added.selectedTools().len()).to_equal(1)

val removed = added.toggle("write")
expect(removed.state.lastAction).to_equal("remove write")
expect(removed.selectedTools().len()).to_equal(0)

val blocked = selector.toggle("web-fetch")
expect(blocked.state.lastAction).to_equal("blocked web-fetch")
expect(blocked.selectedTools().len()).to_equal(0)
```

</details>

#### filters by search source and disabled visibility

- Search available tools across text and source
   - Expected: filterToolSelectorTools(tools, "workspace", "all", true).len() equals `1`
   - Expected: filterToolSelectorTools(tools, "shell", "project", true)[0].id equals `bash`
   - Expected: filterToolSelectorTools(tools, "", "builtin", true).len() equals `2`
   - Expected: visible.len() equals `1`
   - Expected: visible[0].id equals `bash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Search available tools across text and source")
val tools = sampleToolSelectorTools()
expect(filterToolSelectorTools(tools, "workspace", "all", true).len()).to_equal(1)
expect(filterToolSelectorTools(tools, "shell", "project", true)[0].id).to_equal("bash")
expect(filterToolSelectorTools(tools, "", "builtin", true).len()).to_equal(2)

val visible = visibleToolSelectorTools(tools, ToolSelectorState.new("", "project", [], false, "filter"))
expect(visible.len()).to_equal(1)
expect(visible[0].id).to_equal("bash")
expect(findToolSelectorToolById(tools, "missing")).to_be_nil()
```

</details>

#### renders summary rows and empty states

- Render header, query badge, disabled badge, and empty filters
   - Expected: empty equals `No tools match search "web" and source User and enabled tools`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render header, query badge, disabled badge, and empty filters")
val selector = createToolSelector(sampleToolSelectorTools()).filter("web", "user")
val output = selector.render()
expect(output).to_contain("Tools 1/5")
expect(output).to_contain("User")
expect(output).to_contain("search:web")
expect(output).to_contain("[ ] Web Fetch [User] disabled")

val empty = selector.hideDisabled().render()
expect(empty).to_equal("No tools match search \"web\" and source User and enabled tools")
```

</details>

#### exports source helper parity

- Pin source labels and upstream helper names
   - Expected: toolSelectorSourceDisplayName("built-in") equals `Built-in`
   - Expected: toolSelectorSourceDisplayName("project") equals `Project`
   - Expected: toolSelectorModeledSourceFile() equals `src/components/agents/ToolSelector.tsx`
   - Expected: toolSelectorModeledSourceHelper() equals `getAvailableTools`
   - Expected: toolSelectorModeledToggleHelper() equals `toggleToolSelection`
   - Expected: toolSelectorModeledSummaryHelper() equals `getToolSelectionSummary`
   - Expected: toolSelectorSourceLinesModeled() equals `561`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source labels and upstream helper names")
expect(toolSelectorSourceDisplayName("built-in")).to_equal("Built-in")
expect(toolSelectorSourceDisplayName("project")).to_equal("Project")
expect(toolSelectorSourceOptions()).to_contain("all")
expect(toolSelectorSourceOptions()).to_contain("project")
expect(toolSelectorSourceOptions()).to_contain("user")
expect(toolSelectorSourceOptions()).to_contain("builtin")
expect(toolSelectorModeledSourceFile()).to_equal("src/components/agents/ToolSelector.tsx")
expect(toolSelectorModeledSourceHelper()).to_equal("getAvailableTools")
expect(toolSelectorModeledToggleHelper()).to_equal("toggleToolSelection")
expect(toolSelectorModeledSummaryHelper()).to_equal("getToolSelectionSummary")
expect(toolSelectorSourceLinesModeled()).to_equal(561)
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
