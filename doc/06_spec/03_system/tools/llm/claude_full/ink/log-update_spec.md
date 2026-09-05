# Claude Full LogUpdate

> This spec pins the Claude Ink `log-update.ts` parity slice for the Simple `llm_caret` mirror. The source file is intentionally hyphenated to match the upstream TypeScript path, so the executable checks read the owned implementation file and assert the class layout, source-line ledger, and modeled render behaviors directly.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full LogUpdate

This spec pins the Claude Ink `log-update.ts` parity slice for the Simple `llm_caret` mirror. The source file is intentionally hyphenated to match the upstream TypeScript path, so the executable checks read the owned implementation file and assert the class layout, source-line ledger, and modeled render behaviors directly.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/tools/llm/claude_full/ink/log-update_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec pins the Claude Ink `log-update.ts` parity slice for the Simple
`llm_caret` mirror. The source file is intentionally hyphenated to match the
upstream TypeScript path, so the executable checks read the owned implementation
file and assert the class layout, source-line ledger, and modeled render
behaviors directly.

## Examples

The implementation must keep `LogUpdate` at source line 43, `VirtualScreen` at
source line 752, and total modeled source parity at 773 lines.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Scenarios

### Claude full LogUpdate source parity

#### should keep exact source LOC and class line positions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should keep exact source LOC and class line positions
- Read the owned log-update implementation
   - Expected: file_exists(sourcePath()) is true
   - Expected: sourceLineCount() equals `773`
   - Expected: lineAt(43) equals `class LogUpdate:`
   - Expected: lineAt(752) equals `class VirtualScreen:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep exact source LOC and class line positions")
step("Read the owned log-update implementation")
expect(file_exists(sourcePath())).to_equal(true)
expect(sourceLineCount()).to_equal(773)
expect(lineAt(43)).to_equal("class LogUpdate:")
expect(lineAt(752)).to_equal("class VirtualScreen:")
```

</details>

#### should include LogUpdate state, reset, deprecated done cleanup, and render paths

- should include LogUpdate state, reset, deprecated done cleanup, and render paths
- Check LogUpdate behavior is represented in source


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should include LogUpdate state, reset, deprecated done cleanup, and render paths")
step("Check LogUpdate behavior is represented in source")
val source = sourceText()
expect(source).to_contain("previousOutput: text")
expect(source).to_contain("me renderPreviousOutput_DEPRECATED(prevFrame: LogFrame) -> [LogDiffOp]:")
expect(source).to_contain("me reset() -> ():")
expect(source).to_contain("me render(prev: LogFrame, next: LogFrame, altScreen: bool, decstbmSafe: bool) -> [LogDiffOp]:")
expect(source).to_contain("return fullResetSequence_CAUSES_FLICKER(next, \"resize\")")
expect(source).to_contain("return fullResetSequence_CAUSES_FLICKER(next, \"offscreen\")")
```

</details>

#### should include virtual cursor transactions and terminal diff operations

- should include virtual cursor transactions and terminal diff operations
- Check VirtualScreen and diff op modeling


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should include virtual cursor transactions and terminal diff operations")
step("Check VirtualScreen and diff op modeling")
val source = sourceText()
expect(source).to_contain("class LogDiffOp:")
expect(source).to_contain("static fn stdout(content: text) -> LogDiffOp:")
expect(source).to_contain("static fn clearTerminal(reason: text) -> LogDiffOp:")
expect(source).to_contain("class VirtualScreen:")
expect(source).to_contain("me txn(patches: [LogDiffOp], dx: i64, dy: i64) -> ():")
expect(source).to_contain("me.cursor.x = me.cursor.x + dx")
expect(source).to_contain("me.cursor.y = me.cursor.y + dy")
```

</details>

#### should cover full-frame render, cursor movement, scroll hints, and width compensation

- should cover full-frame render, cursor movement, scroll hints, and width compensation
- Check source-led behavior helpers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cover full-frame render, cursor movement, scroll hints, and width compensation")
step("Check source-led behavior helpers")
val source = sourceText()
expect(source).to_contain("fn joinTrimmedLines(lines: [text]) -> text:")
expect(source).to_contain("fn trimRightSpaces(value: text) -> text:")
expect(source).to_contain("fn moveCursorTo(screen: VirtualScreen, targetX: i64, targetY: i64) -> ():")
expect(source).to_contain("scroll:\" + next.scrollTop.to_text()")
expect(source).to_contain("fn needsWidthCompensation(char: text) -> bool:")
expect(source).to_contain("fn writeCellWithStyleStr(screen: VirtualScreen, char: text, cellWidth: i64, styleStr: text) -> bool:")
```

</details>

#### should expose the source-line ledger function and avoid placeholder spec passes

- should expose the source-line ledger function and avoid placeholder spec passes
- Check executable assertions pin the ledger


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the source-line ledger function and avoid placeholder spec passes")
step("Check executable assertions pin the ledger")
val source = sourceText()
expect(source).to_contain("fn logUpdateSourceLinesModeled() -> i64:")
expect(source).to_contain("    773")
expect(source).to_contain("# Source parity ledger 057: source line 752 maps to class VirtualScreen in this file.")
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

- Canonical SPipe generation for source `e56b8e77726f6d7c4caacec843228a77d8910fd1d1f4fe44dee2f7771cce1474`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e56b8e77726f6d7c4caacec843228a77d8910fd1d1f4fe44dee2f7771cce1474`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e56b8e77726f6d7c4caacec843228a77d8910fd1d1f4fe44dee2f7771cce1474`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/ink/log-update_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/log-update_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=75 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/log-update_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/log-update_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/log-update_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/ink/log-update_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep exact source LOC and class line positions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/log-update_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep exact source LOC and class line positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/log-update_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include LogUpdate state, reset, deprecated done cleanup, and render paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/log-update_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include LogUpdate state, reset, deprecated done cleanup, and render paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/log-update_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include virtual cursor transactions and terminal diff operations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/log-update_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include virtual cursor transactions and terminal diff operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/log-update_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cover full-frame render, cursor movement, scroll hints, and width compensation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/log-update_spec.spl:100:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the source-line ledger function and avoid placeholder spec passes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
