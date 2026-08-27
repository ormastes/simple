# Claude Full DiffFileList Component

> Checks modern SSpec parity for diff file list filtering, navigation, and rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full DiffFileList Component

Checks modern SSpec parity for diff file list filtering, navigation, and rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for diff file list filtering, navigation, and rendering.

## Scenarios

### Claude full DiffFileList component

#### should filter and render changed files

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should filter and render changed files
- Create sample diff file list
   - Expected: visible.len() equals `1`
   - Expected: visible[0].path equals `src/app/App.spl`
- Render filtered rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should filter and render changed files")
step("Create sample diff file list")
val files = sampleDiffFileItems()
val state = DiffFileListState.new("app", "modified", "", false)
val visible = visibleDiffFiles(files, state)
expect(visible.len()).to_equal(1)
expect(visible[0].path).to_equal("src/app/App.spl")

step("Render filtered rows")
val output = renderDiffFileList(files, state)
expect(output).to_contain("Diff files")
expect(output).to_contain("src/app/App.spl")
expect(output).to_contain("+12 -3")
```

</details>

#### should handle keyboard navigation and grouped summaries

- should handle keyboard navigation and grouped summaries
- Navigate through diff files
   - Expected: handleDiffFileListKey(files, state, "down").selectedPath equals `src/app/App.spl`
   - Expected: handleDiffFileListKey(files, state, "end").selectedPath equals `test/old_spec.spl`
- Render grouped file list


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle keyboard navigation and grouped summaries")
step("Navigate through diff files")
val files = sampleDiffFileItems()
val state = DiffFileListState.new("", "all", "README.md", true)
expect(handleDiffFileListKey(files, state, "down").selectedPath).to_equal("src/app/App.spl")
expect(handleDiffFileListKey(files, state, "end").selectedPath).to_equal("test/old_spec.spl")

step("Render grouped file list")
val grouped = renderDiffFileList(files, state)
expect(grouped).to_contain("[src/app]")
expect(grouped).to_contain("grouped")
```

</details>

#### should expose empty state and modeled source floor

- should expose empty state and modeled source floor
- Render empty states
   - Expected: renderDiffFileList(emptyFiles, DiffFileListState.empty()) equals `No changed files`
- Check modeled TypeScript source floor
   - Expected: diffFileListSourceLinesModeled() equals `291`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose empty state and modeled source floor")
step("Render empty states")
val emptyFiles: [DiffFileItem] = []
expect(renderDiffFileList(emptyFiles, DiffFileListState.empty())).to_equal("No changed files")
expect(renderDiffFileList(emptyFiles, DiffFileListState.new("missing", "added", "", false))).to_contain("missing")

step("Check modeled TypeScript source floor")
expect(diffFileListSourceLinesModeled()).to_equal(291)
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

- Canonical SPipe generation for source `70dc64212210fa5487a7e372e2a7cbf470989a54bab723f61e5ad5e49e1a4597`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70dc64212210fa5487a7e372e2a7cbf470989a54bab723f61e5ad5e49e1a4597`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70dc64212210fa5487a7e372e2a7cbf470989a54bab723f61e5ad5e49e1a4597`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/diff_file_list_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/diff_file_list_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/diff_file_list_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should filter and render changed files' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should filter and render changed files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle keyboard navigation and grouped summaries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle keyboard navigation and grouped summaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose empty state and modeled source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/diff_file_list_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose empty state and modeled source floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
