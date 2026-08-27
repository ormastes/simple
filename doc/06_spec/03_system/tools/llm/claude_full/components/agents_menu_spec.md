# Claude Full AgentsMenu Component

> Checks modeled open-close state, selection, filtering, action summaries, and source helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full AgentsMenu Component

Checks modeled open-close state, selection, filtering, action summaries, and source helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/agents_menu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modeled open-close state, selection, filtering, action summaries, and source helpers.

## Scenarios

### Claude full AgentsMenu component

#### opens closes toggles and normalizes selection

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens closes toggles and normalizes selection
- Create closed menu and open it
   - Expected: closed.state.isOpen is false
   - Expected: closed.render() equals `Agents menu closed`
   - Expected: opened.state.isOpen is true
   - Expected: opened.state.selectedId equals `docs`
   - Expected: opened.state.lastAction equals `open`
   - Expected: opened.close().state.isOpen is false
   - Expected: opened.toggle().state.isOpen is false
   - Expected: closed.toggle().state.isOpen is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("opens closes toggles and normalizes selection")
step("Create closed menu and open it")
val items = sampleAgentsMenuItems()
val closed = createAgentsMenu(items)
expect(closed.state.isOpen).to_equal(false)
expect(closed.render()).to_equal("Agents menu closed")

val opened = closed.open()
expect(opened.state.isOpen).to_equal(true)
expect(opened.state.selectedId).to_equal("docs")
expect(opened.state.lastAction).to_equal("open")
expect(opened.close().state.isOpen).to_equal(false)
expect(opened.toggle().state.isOpen).to_equal(false)
expect(closed.toggle().state.isOpen).to_equal(true)
```

</details>

#### filters by query and source

- filters by query and source
- Search matches description, tools, and source filters
   - Expected: filterAgentsMenuItems(items, "test plans", "user").len() equals `1`
   - Expected: filterAgentsMenuItems(items, "Write", "builtin")[0].id equals `docs`
   - Expected: filterAgentsMenuItems(items, "sonnet", "all").len() equals `2`
   - Expected: visible.len() equals `1`
   - Expected: visible[0].name equals `Docs`
   - Expected: model.state.selectedId equals `docs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters by query and source")
step("Search matches description, tools, and source filters")
val items = sampleAgentsMenuItems()
expect(filterAgentsMenuItems(items, "test plans", "user").len()).to_equal(1)
expect(filterAgentsMenuItems(items, "Write", "builtin")[0].id).to_equal("docs")
expect(filterAgentsMenuItems(items, "sonnet", "all").len()).to_equal(2)

val model = openAgentsMenu(items).filter("release", "built-in")
val visible = model.visibleItems()
expect(visible.len()).to_equal(1)
expect(visible[0].name).to_equal("Docs")
expect(model.state.selectedId).to_equal("docs")
```

</details>

#### sorts and moves selection with wrapping

- sorts and moves selection with wrapping
- Sort by name/id and select next previous
   - Expected: sorted[0].id equals `a`
   - Expected: sorted[1].id equals `m`
   - Expected: sorted[2].id equals `z`
   - Expected: selectNextAgentsMenuItem(items, state).selectedId equals `z`
   - Expected: selectPreviousAgentsMenuItem(items, state).selectedId equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sorts and moves selection with wrapping")
step("Sort by name/id and select next previous")
val items = [
    AgentsMenuItem.new("z", "Zeta", "last", "project", "sonnet", true, []),
    AgentsMenuItem.new("a", "Alpha", "first", "user", "haiku", true, []),
    AgentsMenuItem.new("m", "Middle", "middle", "builtin", "sonnet", false, [])
]
val sorted = sortAgentsMenuItems(items)
expect(sorted[0].id).to_equal("a")
expect(sorted[1].id).to_equal("m")
expect(sorted[2].id).to_equal("z")
val state = AgentsMenuState.new(true, "", "all", "m", "")
expect(selectNextAgentsMenuItem(items, state).selectedId).to_equal("z")
expect(selectPreviousAgentsMenuItem(items, state).selectedId).to_equal("a")
expect(findAgentsMenuItemById(items, "missing")).to_be_nil()
```

</details>

#### renders menu rows empty states and action summaries

- renders menu rows empty states and action summaries
- Render selected row and action text
   - Expected: opened.actionSummary() equals `select review | run enabled | edit enabled`
   - Expected: agentsMenuActionSummary(items[2]) equals `select docs | run disabled | edit enabled`
   - Expected: renderAgentsMenu([], AgentsMenuState.new(true, "", "all", "", "open")) equals `No agents configured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders menu rows empty states and action summaries")
step("Render selected row and action text")
val items = sampleAgentsMenuItems()
val opened = openAgentsMenu(items).select("review")
val output = opened.render()
expect(output).to_contain("Agents menu 3/3")
expect(output).to_contain("> Review [Project] enabled")
expect(output).to_contain("sonnet")
expect(opened.actionSummary()).to_equal("select review | run enabled | edit enabled")
expect(agentsMenuActionSummary(items[2])).to_equal("select docs | run disabled | edit enabled")

val empty = renderAgentsMenu(items, AgentsMenuState.new(true, "missing", "project", "", "filter"))
expect(empty).to_contain("No agents match search \"missing\" and source Project")
expect(renderAgentsMenu([], AgentsMenuState.new(true, "", "all", "", "open"))).to_equal("No agents configured")
```

</details>

#### exports source helper parity

- exports source helper parity
- Pin source labels and upstream helper names
   - Expected: agentsMenuSourceDisplayName("built-in") equals `Built-in`
   - Expected: agentsMenuSourceDisplayName("project") equals `Project`
   - Expected: agentsMenuModeledSourceFile() equals `src/components/agents/AgentsMenu.tsx`
   - Expected: agentsMenuModeledSourceHelper() equals `getAgentDefinitionsWithOverrides`
   - Expected: agentsMenuModeledMenuHook() equals `useAgentsMenu`
   - Expected: agentsMenuModeledActionCount() equals `3`
   - Expected: agentsMenuSourceLinesModeled() equals `799`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source helper parity")
step("Pin source labels and upstream helper names")
expect(agentsMenuSourceDisplayName("built-in")).to_equal("Built-in")
expect(agentsMenuSourceDisplayName("project")).to_equal("Project")
expect(agentsMenuSourceOptions()).to_contain("all")
expect(agentsMenuSourceOptions()).to_contain("project")
expect(agentsMenuSourceOptions()).to_contain("user")
expect(agentsMenuSourceOptions()).to_contain("builtin")
expect(agentsMenuModeledSourceFile()).to_equal("src/components/agents/AgentsMenu.tsx")
expect(agentsMenuModeledSourceHelper()).to_equal("getAgentDefinitionsWithOverrides")
expect(agentsMenuModeledMenuHook()).to_equal("useAgentsMenu")
expect(agentsMenuModeledActionCount()).to_equal(3)
expect(agentsMenuSourceLinesModeled()).to_equal(799)
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

- Canonical SPipe generation for source `d4c405e225b48cc8edc909361edbd11a318c87033c182f6344eb10c5b0d0b4dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4c405e225b48cc8edc909361edbd11a318c87033c182f6344eb10c5b0d0b4dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4c405e225b48cc8edc909361edbd11a318c87033c182f6344eb10c5b0d0b4dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/agents_menu_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/agents_menu_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/agents_menu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/agents_menu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/agents_menu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/agents_menu_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens closes toggles and normalizes selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/agents_menu_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters by query and source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/agents_menu_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts and moves selection with wrapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
