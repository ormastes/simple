# Claude Full AgentsList Component

> Checks the modeled list filtering, sorting, selection, empty state, and source helpers.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the modeled list filtering, sorting, selection, empty state, and source helpers.

## Scenarios

### Claude full AgentsList component

#### filters by query and source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- filters by query and source
- Search matches description, source filter narrows visible rows
   - Expected: visible.len() equals `1`
   - Expected: visible[0].id equals `agent-qa`
   - Expected: filterAgents(items, "sonnet", "all").len() equals `2`
   - Expected: filterAgents(items, "Write", "builtin")[0].name equals `Docs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters by query and source")
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

- sorts by name and keeps selection stable
- Unsorted input renders alphabetically and selection moves with wrapping
   - Expected: sorted[0].id equals `a`
   - Expected: sorted[1].id equals `m`
   - Expected: sorted[2].id equals `z`
   - Expected: selectNextAgent(items, selected).selectedId equals `z`
   - Expected: selectPreviousAgent(items, selected).selectedId equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sorts by name and keeps selection stable")
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

- renders selected rows and summaries
- Render includes header counts, selected marker, source label, and summary parts


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders selected rows and summaries")
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

- normalizes empty state and model selection
- No matches explain the active filters; models clamp selection to first visible row
   - Expected: renderAgentsEmptyState(AgentsListState.new("", "all", "")) equals `agentsListEmptyMessage()`
   - Expected: model.state.selectedId equals `agent-docs`
   - Expected: model.selectedItem() == nil is false
   - Expected: selected.name equals `Docs`
   - Expected: createAgentsList([]).render() equals `agentsListEmptyMessage()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes empty state and model selection")
step("No matches explain the active filters; models clamp selection to first visible row")
val items = sampleAgentsListItems()
val emptyState = AgentsListState.new("missing", "project", "")
expect(renderAgentsEmptyState(AgentsListState.new("", "all", ""))).to_equal(agentsListEmptyMessage())
expect(renderAgentsList(items, emptyState)).to_contain("No agents match search \"missing\" and source Project")
val model = AgentsListModel.new(items, AgentsListState.new("docs", "builtin", "agent-review"))
expect(model.state.selectedId).to_equal("agent-docs")
expect(model.selectedItem() == nil).to_equal(false)
if val Some(selected) = model.selectedItem():
    expect(selected.name).to_equal("Docs")
expect(createAgentsList([]).render()).to_equal(agentsListEmptyMessage())
```

</details>

#### exports source helper parity

- exports source helper parity
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

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source helper parity")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38f54c7fad231ef34a5a90676b3316b0883607a7a80c88150705495e03e55445`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38f54c7fad231ef34a5a90676b3316b0883607a7a80c88150705495e03e55445`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38f54c7fad231ef34a5a90676b3316b0883607a7a80c88150705495e03e55445`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/agents_list_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/agents_list_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/agents_list_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/agents_list_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/agents_list_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/agents_list_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters by query and source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/agents_list_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts by name and keeps selection stable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/agents_list_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders selected rows and summaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
