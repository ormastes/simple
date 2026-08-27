# Claude Full GlobalSearchDialog Component

> Checks global search query state, scoring, grouped rows, keyboard navigation, and summaries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full GlobalSearchDialog Component

Checks global search query state, scoring, grouped rows, keyboard navigation, and summaries.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/global_search_dialog_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks global search query state, scoring, grouped rows, keyboard navigation, and summaries.

## Scenarios

### Claude full GlobalSearchDialog component

#### opens closes queries and normalizes selection

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens closes queries and normalizes selection
- Create a closed dialog and open it
   - Expected: closed.state.isOpen is false
   - Expected: closed.render() equals `Global search closed`
   - Expected: opened.state.isOpen is true
   - Expected: opened.state.selectedIndex equals `0`
   - Expected: opened.state.lastAction equals `open`
   - Expected: opened.query("keyboard").state.query equals `keyboard`
   - Expected: opened.close().state.isOpen is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("opens closes queries and normalizes selection")
step("Create a closed dialog and open it")
val results = sampleGlobalSearchResults()
val closed = createGlobalSearchDialog(results)
expect(closed.state.isOpen).to_equal(false)
expect(closed.render()).to_equal("Global search closed")

val opened = closed.open()
expect(opened.state.isOpen).to_equal(true)
expect(opened.state.selectedIndex).to_equal(0)
expect(opened.state.lastAction).to_equal("open")
expect(opened.query("keyboard").state.query).to_equal("keyboard")
expect(opened.close().state.isOpen).to_equal(false)
```

</details>

#### scores and filters rows

- scores and filters rows
- Search title, subtitle, path, and keywords
   - Expected: keyboardRows.len() equals `1`
   - Expected: keyboardRows[0].result.id equals `help-shortcuts`
   - Expected: fileRows.len() equals `1`
   - Expected: fileRows[0].result.path equals `AGENTS.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scores and filters rows")
step("Search title, subtitle, path, and keywords")
val results = sampleGlobalSearchResults()
val keyboardRows = globalSearchRowsForQuery(results, "keyboard", "all")
expect(keyboardRows.len()).to_equal(1)
expect(keyboardRows[0].result.id).to_equal("help-shortcuts")
expect(globalSearchScore(results[0], "review")).to_be_greater_than(globalSearchScore(results[0], "diff"))

val fileRows = globalSearchRowsForQuery(results, "agent", "files")
expect(fileRows.len()).to_equal(1)
expect(fileRows[0].result.path).to_equal("AGENTS.md")
```

</details>

#### groups categories and renders selected rows

- groups categories and renders selected rows
- Render grouped rows with selected marker
   - Expected: groups.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("groups categories and renders selected rows")
step("Render grouped rows with selected marker")
val model = openGlobalSearchDialog(sampleGlobalSearchResults()).query("claude")
val groups = groupGlobalSearchRows(model.rows())
expect(groups.len()).to_equal(2)
val output = model.render()
expect(output).to_contain("Global search 2/7")
expect(output).to_contain("Commands")
expect(output).to_contain("Sessions")
expect(output).to_contain("> Switch model [Commands] enabled")
```

</details>

#### handles keyboard navigation and summaries

- handles keyboard navigation and summaries
- Move through result rows and close with Escape
   - Expected: model.handleKey("ArrowDown").state.selectedIndex equals `1`
   - Expected: model.handleKey("ArrowUp").state.selectedIndex equals `6`
   - Expected: model.handleKey("End").state.selectedIndex equals `6`
   - Expected: model.handleKey("Home").state.selectedIndex equals `0`
   - Expected: model.handleKey("Enter").state.lastAction equals `submit`
   - Expected: model.handleKey("Escape").state.isOpen is false
   - Expected: model.loading().summary() equals `loading`
   - Expected: model.fail("index unavailable").summary() equals `error: index unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles keyboard navigation and summaries")
step("Move through result rows and close with Escape")
val model = openGlobalSearchDialog(sampleGlobalSearchResults())
expect(model.handleKey("ArrowDown").state.selectedIndex).to_equal(1)
expect(model.handleKey("ArrowUp").state.selectedIndex).to_equal(6)
expect(model.handleKey("End").state.selectedIndex).to_equal(6)
expect(model.handleKey("Home").state.selectedIndex).to_equal(0)
expect(model.handleKey("Enter").state.lastAction).to_equal("submit")
expect(model.handleKey("Escape").state.isOpen).to_equal(false)
expect(model.loading().summary()).to_equal("loading")
expect(model.fail("index unavailable").summary()).to_equal("error: index unavailable")
```

</details>

#### renders empty loading error and source helpers

- renders empty loading error and source helpers
- Pin summaries and upstream helper names
   - Expected: renderGlobalSearchDialog(results, GlobalSearchDialogState.new(true, "missing", "help", 0, false, "", "query")) equals `No global search results for search "missing" and category Help`
   - Expected: renderGlobalSearchDialog(results, GlobalSearchDialogState.new(true, "read", "all", 0, true, "", "loading")) equals `Global search loading · search:read`
   - Expected: renderGlobalSearchDialog(results, GlobalSearchDialogState.new(true, "", "all", 0, false, "boom", "error")) equals `Global search error: boom`
   - Expected: globalSearchCategoryLabel("session") equals `Sessions`
   - Expected: globalSearchModeledSourceFile() equals `src/components/GlobalSearchDialog.tsx`
   - Expected: globalSearchModeledHook() equals `useGlobalSearch`
   - Expected: globalSearchModeledKeyboardHelper() equals `handleKeyDown`
   - Expected: globalSearchModeledSourceLines() equals `342`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders empty loading error and source helpers")
step("Pin summaries and upstream helper names")
val results = sampleGlobalSearchResults()
expect(renderGlobalSearchDialog(results, GlobalSearchDialogState.new(true, "missing", "help", 0, false, "", "query"))).to_equal("No global search results for search \"missing\" and category Help")
expect(renderGlobalSearchDialog(results, GlobalSearchDialogState.new(true, "read", "all", 0, true, "", "loading"))).to_equal("Global search loading · search:read")
expect(renderGlobalSearchDialog(results, GlobalSearchDialogState.new(true, "", "all", 0, false, "boom", "error"))).to_equal("Global search error: boom")
expect(globalSearchCategoryLabel("session")).to_equal("Sessions")
expect(globalSearchCategoryOptions()).to_contain("commands")
expect(globalSearchModeledSourceFile()).to_equal("src/components/GlobalSearchDialog.tsx")
expect(globalSearchModeledHook()).to_equal("useGlobalSearch")
expect(globalSearchModeledKeyboardHelper()).to_equal("handleKeyDown")
expect(globalSearchModeledSourceLines()).to_equal(342)
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

- Canonical SPipe generation for source `f3e8a6931442d9dde0af50aa500e28027ff4a167fa34c6205a2cc021b3cfffcd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3e8a6931442d9dde0af50aa500e28027ff4a167fa34c6205a2cc021b3cfffcd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3e8a6931442d9dde0af50aa500e28027ff4a167fa34c6205a2cc021b3cfffcd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/global_search_dialog_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/global_search_dialog_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/global_search_dialog_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/global_search_dialog_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/global_search_dialog_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/global_search_dialog_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens closes queries and normalizes selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/global_search_dialog_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scores and filters rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/global_search_dialog_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups categories and renders selected rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
