# Claude Full ToolSelector Component

> Checks modeled available tools, selected tools, toggles, filtering, disabled tools, summaries, and source helpers.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modeled available tools, selected tools, toggles, filtering, disabled tools, summaries, and source helpers.

## Scenarios

### Claude full ToolSelector component

#### models available and selected tools

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models available and selected tools
- Create a selector and add enabled tools
   - Expected: selector.tools.len() equals `5`
   - Expected: selector.summary() equals `No tools selected`
   - Expected: selected.selectedTools().len() equals `2`
   - Expected: selected.summary() equals `Selected 2 of 5: Bash, Read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models available and selected tools")
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

- toggles enabled tools and blocks disabled tools
- Toggle on, toggle off, and ignore disabled rows
   - Expected: added.state.lastAction equals `add write`
   - Expected: added.selectedTools().len() equals `1`
   - Expected: removed.state.lastAction equals `remove write`
   - Expected: removed.selectedTools().len() equals `0`
   - Expected: blocked.state.lastAction equals `blocked web-fetch`
   - Expected: blocked.selectedTools().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("toggles enabled tools and blocks disabled tools")
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

- filters by search source and disabled visibility
- Search available tools across text and source
   - Expected: filterToolSelectorTools(tools, "workspace", "all", true).len() equals `1`
   - Expected: filterToolSelectorTools(tools, "shell", "project", true)[0].id equals `bash`
   - Expected: filterToolSelectorTools(tools, "", "builtin", true).len() equals `2`
   - Expected: visible.len() equals `1`
   - Expected: visible[0].id equals `bash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters by search source and disabled visibility")
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

- renders summary rows and empty states
- Render header, query badge, disabled badge, and empty filters
   - Expected: empty equals `No tools match search "web" and source User and enabled tools`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders summary rows and empty states")
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

- exports source helper parity
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source helper parity")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eb562c92a51f47fb6ebf0d672ea16be8f5a93fbfd434d3da0f1c08390ec38ffd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb562c92a51f47fb6ebf0d672ea16be8f5a93fbfd434d3da0f1c08390ec38ffd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb562c92a51f47fb6ebf0d672ea16be8f5a93fbfd434d3da0f1c08390ec38ffd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/tool_selector_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/tool_selector_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/tool_selector_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/tool_selector_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/tool_selector_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/tool_selector_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models available and selected tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/tool_selector_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'toggles enabled tools and blocks disabled tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/tool_selector_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters by search source and disabled visibility' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
