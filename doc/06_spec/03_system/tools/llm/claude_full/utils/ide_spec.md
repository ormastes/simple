# Claude Full IDE Utils Slice

> Focused Simple coverage for IDE label/classification helpers from utils/ide.ts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full IDE Utils Slice

Focused Simple coverage for IDE label/classification helpers from utils/ide.ts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/ide_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for IDE label/classification helpers from utils/ide.ts.
UI rendering stays in the Simple/TUI command layer.

## Scenarios

### Claude full IDE utils parity

#### should model IDE family classification

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model IDE family classification
- Check IDE type predicates
   - Expected: isVSCodeIdeRoute("") is false
   - Expected: isVSCodeIdeRoute("vscode") is true
   - Expected: isJetBrainsIdeRoute("intellij") is true
   - Expected: isJetBrainsIdeRoute("cursor") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model IDE family classification")
step("Check IDE type predicates")
expect(isVSCodeIdeRoute("")).to_equal(false)
expect(isVSCodeIdeRoute("vscode")).to_equal(true)
expect(isJetBrainsIdeRoute("intellij")).to_equal(true)
expect(isJetBrainsIdeRoute("cursor")).to_equal(false)
```

</details>

#### should model IDE display names

- should model IDE display names
- Check display labels
   - Expected: toIDEDisplayNameRoute("") equals `IDE`
   - Expected: toIDEDisplayNameRoute("vscode") equals `VS Code`
   - Expected: toIDEDisplayNameRoute("code --wait") equals `VS Code`
   - Expected: toIDEDisplayNameRoute("/usr/bin/cursor") equals `Cursor`
   - Expected: toIDEDisplayNameRoute("unknown-tool") equals `Unknown-tool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model IDE display names")
step("Check display labels")
expect(toIDEDisplayNameRoute("")).to_equal("IDE")
expect(toIDEDisplayNameRoute("vscode")).to_equal("VS Code")
expect(toIDEDisplayNameRoute("code --wait")).to_equal("VS Code")
expect(toIDEDisplayNameRoute("/usr/bin/cursor")).to_equal("Cursor")
expect(toIDEDisplayNameRoute("unknown-tool")).to_equal("Unknown-tool")
```

</details>

#### should model connected IDE helper routes

- should model connected IDE helper routes
- Check connected IDE routes
   - Expected: connectedIdeNameRoute("cursor", true, "vscode") equals `Cursor`
   - Expected: connectedIdeNameRoute("", false, "vscode") equals `null`
   - Expected: connectedIdeNameRoute("", true, "vscode") equals `VS Code`
   - Expected: hasAccessToIDEExtensionDiffFeatureRoute("ide") is true
   - Expected: hasAccessToIDEExtensionDiffFeatureRoute("other") is false
   - Expected: ideUtilsSourceLinesModeled() equals `1494`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model connected IDE helper routes")
step("Check connected IDE routes")
expect(connectedIdeNameRoute("cursor", true, "vscode")).to_equal("Cursor")
expect(connectedIdeNameRoute("", false, "vscode")).to_equal("null")
expect(connectedIdeNameRoute("", true, "vscode")).to_equal("VS Code")
expect(hasAccessToIDEExtensionDiffFeatureRoute("ide")).to_equal(true)
expect(hasAccessToIDEExtensionDiffFeatureRoute("other")).to_equal(false)
expect(ideUtilsSourceLinesModeled()).to_equal(1494)
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

- Canonical SPipe generation for source `379e3f21d677371192a4b758552175172056f4f392bbadc5cf1b51f3ae700cf8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `379e3f21d677371192a4b758552175172056f4f392bbadc5cf1b51f3ae700cf8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `379e3f21d677371192a4b758552175172056f4f392bbadc5cf1b51f3ae700cf8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/ide_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/ide_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/ide_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/ide_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/ide_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/ide_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model IDE family classification' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/ide_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model IDE family classification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/ide_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model IDE display names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/ide_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model IDE display names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/ide_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model connected IDE helper routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/ide_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model connected IDE helper routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
