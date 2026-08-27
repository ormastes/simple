# Claude Full ContextVisualization

> Checks context usage buckets, labels, collapse status, and source grouping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full ContextVisualization

Checks context usage buckets, labels, collapse status, and source grouping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/context_visualization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks context usage buckets, labels, collapse status, and source grouping.

## Scenarios

### Claude full components ContextVisualization

#### models token buckets, percentages, warning thresholds, and labels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models token buckets, percentages, warning thresholds, and labels
- Compute bucket percentage and warning status from max tokens
   - Expected: contextTokenPercentTenths(12500, 100000) equals `125`
   - Expected: contextTokenPercentText(12500, 100000) equals `12.5%`
   - Expected: contextUsageStatus(59) equals `ok`
   - Expected: contextUsageStatus(contextWarningPercent()) equals `warning`
   - Expected: contextUsageStatus(contextCriticalPercent()) equals `critical`
   - Expected: contextStatusLine("claude-sonnet", 40000, 100000, 40) equals `claude-sonnet · 40.0k/100.0k tokens (40%)`
   - Expected: visibleContextCategories(categories).len() equals `1`
   - Expected: hasDeferredMcpTools(categories) is true
   - Expected: contextCategoryLabel(categories[0], 100000) equals `filled Messages: 40.0k tokens (40.0%)`
   - Expected: contextCategoryLabel(categories[1], 100000) equals `  MCP tools: 5.0k tokens (N/A)`
   - Expected: freeSpaceLabel(categories, 100000) equals `free Free space: 55.0k (55.0%)`
   - Expected: autocompactLabel(categories, 100000) equals `reserved Autocompact buffer: 2.0k tokens (2.0%)`
   - Expected: buckets[0].label equals `Messages`
   - Expected: buckets[0].percentTenths equals `400`
   - Expected: buckets[1].deferred is true
   - Expected: contextGridSymbol(ContextGridSquare.new("Messages", "primary", 70)) equals `full`
   - Expected: contextGridSymbol(ContextGridSquare.new("Messages", "primary", 69)) equals `partial`
   - Expected: contextGridSymbol(ContextGridSquare.new("Free space", "gray", 0)) equals `free`
   - Expected: contextGridSymbol(ContextGridSquare.new(reservedCategoryName(), "warning", 0)) equals `reserved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models token buckets, percentages, warning thresholds, and labels")
step("Compute bucket percentage and warning status from max tokens")
val categories = [
    ContextCategory.new("Messages", 40000, "primary", false),
    ContextCategory.new("MCP tools", 5000, "secondary", true),
    ContextCategory.new("Empty", 0, "gray", false),
    ContextCategory.new("Free space", 55000, "gray", false),
    ContextCategory.new(reservedCategoryName(), 2000, "warning", false),
]

expect(contextTokenPercentTenths(12500, 100000)).to_equal(125)
expect(contextTokenPercentText(12500, 100000)).to_equal("12.5%")
expect(contextUsageStatus(59)).to_equal("ok")
expect(contextUsageStatus(contextWarningPercent())).to_equal("warning")
expect(contextUsageStatus(contextCriticalPercent())).to_equal("critical")
expect(contextStatusLine("claude-sonnet", 40000, 100000, 40)).to_equal("claude-sonnet · 40.0k/100.0k tokens (40%)")
expect(visibleContextCategories(categories).len()).to_equal(1)
expect(hasDeferredMcpTools(categories)).to_equal(true)
expect(contextCategoryLabel(categories[0], 100000)).to_equal("filled Messages: 40.0k tokens (40.0%)")
expect(contextCategoryLabel(categories[1], 100000)).to_equal("  MCP tools: 5.0k tokens (N/A)")
expect(freeSpaceLabel(categories, 100000)).to_equal("free Free space: 55.0k (55.0%)")
expect(autocompactLabel(categories, 100000)).to_equal("reserved Autocompact buffer: 2.0k tokens (2.0%)")

val buckets = contextTokenBuckets(categories, 100000)
expect(buckets[0].label).to_equal("Messages")
expect(buckets[0].percentTenths).to_equal(400)
expect(buckets[1].deferred).to_equal(true)
expect(contextGridSymbol(ContextGridSquare.new("Messages", "primary", 70))).to_equal("full")
expect(contextGridSymbol(ContextGridSquare.new("Messages", "primary", 69))).to_equal("partial")
expect(contextGridSymbol(ContextGridSquare.new("Free space", "gray", 0))).to_equal("free")
expect(contextGridSymbol(ContextGridSquare.new(reservedCategoryName(), "warning", 0))).to_equal("reserved")
```

</details>

#### groups source-backed items in Claude display order with token sorting

- groups source-backed items in Claude display order with token sorting
- Project, User, Managed, Plugin, Built-in order wins over input order
   - Expected: groups.len() equals `4`
   - Expected: groups[0].sourceDisplay equals `Project`
   - Expected: groups[1].sourceDisplay equals `User`
   - Expected: groups[1].items[0].name equals `user-big`
   - Expected: groups[1].items[1].name equals `user-small`
   - Expected: groups[2].sourceDisplay equals `Plugin`
   - Expected: groups[3].sourceDisplay equals `Built-in`
   - Expected: sourceSummaryLine("Memory files", "/memory", items) equals `Memory files · /memory · 5 sources`
   - Expected: renderSourceGroups(items) equals `["Project", "└ project: 20 tokens", "User", "└ user-big: 30 tokens", "└... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("groups source-backed items in Claude display order with token sorting")
step("Project, User, Managed, Plugin, Built-in order wins over input order")
val items = [
    SourceItem.new("z-plugin", "plugin", 10),
    SourceItem.new("user-big", "user", 30),
    SourceItem.new("project", "project", 20),
    SourceItem.new("user-small", "user", 5),
    SourceItem.new("builtin", "built-in", 9),
]

val groups = groupBySource(items)
expect(groups.len()).to_equal(4)
expect(groups[0].sourceDisplay).to_equal("Project")
expect(groups[1].sourceDisplay).to_equal("User")
expect(groups[1].items[0].name).to_equal("user-big")
expect(groups[1].items[1].name).to_equal("user-small")
expect(groups[2].sourceDisplay).to_equal("Plugin")
expect(groups[3].sourceDisplay).to_equal("Built-in")
expect(sourceSummaryLine("Memory files", "/memory", items)).to_equal("Memory files · /memory · 5 sources")
expect(renderSourceGroups(items)).to_equal(["Project", "└ project: 20 tokens", "User", "└ user-big: 30 tokens", "└ user-small: 5 tokens", "Plugin", "└ z-plugin: 10 tokens", "Built-in", "└ builtin: 9 tokens"])
```

</details>

#### renders collapse summary, warnings, and context visualization lines

- renders collapse summary, warnings, and context visualization lines
- Collapse helper mirrors summarized, staged, error, idle, and disabled states
   - Expected: collapseStatusLine(disabled) equals ``
   - Expected: collapseStatusSummary(waiting) equals `waiting for first trigger`
   - Expected: collapseStatusLine(waiting) equals `Context strategy: collapse (waiting for first trigger)`
   - Expected: collapseStatusSummary(active) equals `2 spans summarized (7 msgs), 1 staged`
   - Expected: collapseStatusSummary(idle) equals `3 spawns, nothing staged yet`
   - Expected: collapseStatusWarning(idle) equals `Collapse idle: 3 consecutive empty runs`
   - Expected: rendered[0] equals `Context Usage`
   - Expected: rendered[1] equals `opus · 60.0k/100.0k tokens (60%)`
   - Expected: contextVisualizationSourceLinesModeled() equals `488`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders collapse summary, warnings, and context visualization lines")
step("Collapse helper mirrors summarized, staged, error, idle, and disabled states")
val disabled = CollapseStatusInput.disabled()
expect(collapseStatusLine(disabled)).to_equal("")

val waiting = CollapseStatusInput.emptyEnabled()
expect(collapseStatusSummary(waiting)).to_equal("waiting for first trigger")
expect(collapseStatusLine(waiting)).to_equal("Context strategy: collapse (waiting for first trigger)")

val active = CollapseStatusInput(enabled: true, collapsedSpans: 2, collapsedMessages: 7, stagedSpans: 1, totalSpawns: 4, totalErrors: 1, lastError: "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnop", emptySpawnWarningEmitted: false, totalEmptySpawns: 0)
expect(collapseStatusSummary(active)).to_equal("2 spans summarized (7 msgs), 1 staged")
expect(collapseStatusWarning(active)).to_contain("Collapse errors: 1/4 spawns failed")
expect(collapseStatusWarning(active)).to_contain("last: abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefgh")

val idle = CollapseStatusInput(enabled: true, collapsedSpans: 0, collapsedMessages: 0, stagedSpans: 0, totalSpawns: 3, totalErrors: 0, lastError: "", emptySpawnWarningEmitted: true, totalEmptySpawns: 3)
expect(collapseStatusSummary(idle)).to_equal("3 spawns, nothing staged yet")
expect(collapseStatusWarning(idle)).to_equal("Collapse idle: 3 consecutive empty runs")

val categories = [
    ContextCategory.new("Messages", 60000, "primary", false),
    ContextCategory.new("Free space", 40000, "gray", false),
]
val rendered = renderContextVisualization("opus", 60000, 100000, 60, categories, waiting)
expect(rendered[0]).to_equal("Context Usage")
expect(rendered[1]).to_equal("opus · 60.0k/100.0k tokens (60%)")
expect(rendered).to_contain("Context strategy: collapse (waiting for first trigger)")
expect(rendered).to_contain("Estimated usage by category")
expect(rendered).to_contain("filled Messages: 60.0k tokens (60.0%)")
expect(contextVisualizationSourceLinesModeled()).to_equal(488)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `48852714d96cc4e92f3298a08c744b22a08eb63223602d3eb6827ea461fd473f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48852714d96cc4e92f3298a08c744b22a08eb63223602d3eb6827ea461fd473f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48852714d96cc4e92f3298a08c744b22a08eb63223602d3eb6827ea461fd473f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/context_visualization_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/context_visualization_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/context_visualization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/context_visualization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/context_visualization_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/context_visualization_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models token buckets, percentages, warning thresholds, and labels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/context_visualization_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups source-backed items in Claude display order with token sorting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/context_visualization_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders collapse summary, warnings, and context visualization lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
