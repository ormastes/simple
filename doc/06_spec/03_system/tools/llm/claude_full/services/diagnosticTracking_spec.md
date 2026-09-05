# Claude Full Diagnostic Tracking

> Purpose: should initialize once and clear state on shutdown

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Diagnostic Tracking

Purpose: should initialize once and clear state on shutdown

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for `tmp/claude/claude-code-main/src/services/diagnosticTracking.ts`. |
| Research | N/A - upstream TypeScript file is the source reference. |
| Source | `test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should initialize once and clear state on shutdown
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Diagnostic Tracking

## Overview

Checks diagnostic baseline tracking, `_claude_fs_right` preference, path
normalization, query lifecycle reset, and human-readable summary formatting for
the Claude CLI `diagnosticTracking.ts` parity slice.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for `tmp/claude/claude-code-main/src/services/diagnosticTracking.ts`.
**Research:** N/A - upstream TypeScript file is the source reference.

## Scenarios

### Claude full diagnosticTracking

#### should initialize once and clear state on shutdown

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should initialize once and clear state on shutdown
- Verify: should initialize once and clear state on shutdown
- Initialize and shutdown the service
   - Expected: service.initialized is true
   - Expected: service.mcpConnected is true
   - Expected: service.initialized is false
   - Expected: service.baselineKeys.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should initialize once and clear state on shutdown")
step("Verify: should initialize once and clear state on shutdown")
# @req: REQ-TOOLS-Diag-001
step("Initialize and shutdown the service")
val service = DiagnosticTrackingService.new()
service.initialize(true)
service.initialize(false)
expect(service.initialized).to_equal(true)
expect(service.mcpConnected).to_equal(true)
service.setBaseline("/a", [Diagnostic.new("old", "Error", 0, 0)])
service.shutdown()
expect(service.initialized).to_equal(false)
expect(service.baselineKeys.len()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should normalize protocol-prefixed file URIs

- should normalize protocol-prefixed file URIs
- Verify: should normalize protocol-prefixed file URIs
- Strip file and claude fs prefixes
   - Expected: service.normalizeFileUri("file:///repo/a.ts") equals `/repo/a.ts`
   - Expected: service.normalizeFileUri("_claude_fs_right:/repo/a.ts") equals `/repo/a.ts`
   - Expected: service.normalizeFileUri("_claude_fs_left:/repo/a.ts") equals `/repo/a.ts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should normalize protocol-prefixed file URIs")
step("Verify: should normalize protocol-prefixed file URIs")
# @req: REQ-TOOLS-Diag-001
step("Strip file and claude fs prefixes")
val service = DiagnosticTrackingService.new()
expect(service.normalizeFileUri("file:///repo/a.ts")).to_equal("/repo/a.ts")
expect(service.normalizeFileUri("_claude_fs_right:/repo/a.ts")).to_equal("/repo/a.ts")
expect(service.normalizeFileUri("_claude_fs_left:/repo/a.ts")).to_equal("/repo/a.ts")
```

</details>

#### should record openFile RPC only when connected

- should record openFile RPC only when connected
- Verify: should record openFile RPC only when connected
- Call ensureFileOpened before and after initialization
   - Expected: service.rpcLog.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record openFile RPC only when connected")
step("Verify: should record openFile RPC only when connected")
# @req: REQ-TOOLS-Diag-001
step("Call ensureFileOpened before and after initialization")
val service = DiagnosticTrackingService.new()
service.ensureFileOpened("/repo/a.ts")
expect(service.rpcLog.len()).to_equal(0)  # oracle: value fixed by the spec contract
service.initialize(true)
service.ensureFileOpened("/repo/a.ts")
expect(service.rpcLog[0]).to_contain("openFile:/repo/a.ts")
```

</details>

#### should capture baseline and log path mismatch

- should capture baseline and log path mismatch
- Verify: should capture baseline and log path mismatch
- Capture before edit diagnostics
   - Expected: service.getBaseline("/repo/a.ts").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should capture baseline and log path mismatch")
step("Verify: should capture baseline and log path mismatch")
# @req: REQ-TOOLS-Diag-001
step("Capture before edit diagnostics")
val service = DiagnosticTrackingService.new()
service.initialize(true)
val diag = Diagnostic.new("old", "Error", 0, 0)
service.beforeFileEdited("/repo/a.ts", [DiagnosticFile.new("file:///repo/a.ts", [diag])], 42)
expect(service.getBaseline("/repo/a.ts").len()).to_equal(1)  # oracle: value fixed by the spec contract
service.beforeFileEdited("/repo/b.ts", [DiagnosticFile.new("file:///repo/a.ts", [diag])], 43)
expect(service.errors[0]).to_contain("Diagnostics file path mismatch")
```

</details>

#### should return only diagnostics not present in baseline

- should return only diagnostics not present in baseline
- Verify: should return only diagnostics not present in baseline
- Compare current diagnostics with baseline
   - Expected: result.len() equals `1`
   - Expected: result[0].diagnostics[0].message equals `new`
   - Expected: service.getBaseline("/repo/a.ts").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return only diagnostics not present in baseline")
step("Verify: should return only diagnostics not present in baseline")
# @req: REQ-TOOLS-Diag-001
step("Compare current diagnostics with baseline")
val service = DiagnosticTrackingService.new()
service.initialize(true)
val old = Diagnostic.new("old", "Warning", 0, 0)
val newDiag = Diagnostic.new("new", "Error", 1, 2)
service.setBaseline("/repo/a.ts", [old])
val result = service.getNewDiagnostics([DiagnosticFile.new("file:///repo/a.ts", [old, newDiag])])
expect(result.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(result[0].diagnostics[0].message).to_equal("new")
expect(service.getBaseline("/repo/a.ts").len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### should prefer changed _claude_fs_right diagnostics

- should prefer changed _claude_fs_right diagnostics
- Verify: should prefer changed _claude_fs_right diagnostics
- Use right-file diagnostics when first seen
   - Expected: result[0].diagnostics[0].message equals `right`
   - Expected: service.getRight("/repo/a.ts").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prefer changed _claude_fs_right diagnostics")
step("Verify: should prefer changed _claude_fs_right diagnostics")
# @req: REQ-TOOLS-Diag-001
step("Use right-file diagnostics when first seen")
val service = DiagnosticTrackingService.new()
service.initialize(true)
service.setBaseline("/repo/a.ts", [])
val fileDiag = Diagnostic.new("left", "Warning", 0, 0)
val rightDiag = Diagnostic.new("right", "Error", 0, 0)
val result = service.getNewDiagnostics([
    DiagnosticFile.new("file:///repo/a.ts", [fileDiag]),
    DiagnosticFile.new("_claude_fs_right:/repo/a.ts", [rightDiag]),
])
expect(result[0].diagnostics[0].message).to_equal("right")
expect(service.getRight("/repo/a.ts").len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should compare diagnostic arrays independent of order

- should compare diagnostic arrays independent of order
- Verify: should compare diagnostic arrays independent of order
- Compare equal arrays in different order
   - Expected: service.areDiagnosticArraysEqual([a, b], [b, a]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should compare diagnostic arrays independent of order")
step("Verify: should compare diagnostic arrays independent of order")
# @req: REQ-TOOLS-Diag-001
step("Compare equal arrays in different order")
val service = DiagnosticTrackingService.new()
val a = Diagnostic.new("a", "Error", 0, 0)
val b = Diagnostic.new("b", "Hint", 1, 1)
expect(service.areDiagnosticArraysEqual([a, b], [b, a])).to_equal(true)
```

</details>

#### should reset on query start after initialization

- should reset on query start after initialization
- Verify: should reset on query start after initialization
- Initialize then start a new query
   - Expected: service.initialized is true
   - Expected: service.baselineKeys.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reset on query start after initialization")
step("Verify: should reset on query start after initialization")
# @req: REQ-TOOLS-Diag-001
step("Initialize then start a new query")
val service = DiagnosticTrackingService.new()
service.handleQueryStart(true)
service.setBaseline("/repo/a.ts", [Diagnostic.new("old", "Info", 0, 0)])
service.handleQueryStart(true)
expect(service.initialized).to_equal(true)
expect(service.baselineKeys.len()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should format diagnostics summary with symbols, code, and source

- should format diagnostics summary with symbols, code, and source
- Verify: should format diagnostics summary with symbols, code, and source
- Format a diagnostic file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should format diagnostics summary with symbols, code, and source")
step("Verify: should format diagnostics summary with symbols, code, and source")
# @req: REQ-TOOLS-Diag-001
step("Format a diagnostic file")
var diag = Diagnostic.new("bad type", "Error", 2, 4)
diag.code = "TS2322"
diag.source = "ts"
val summary = DiagnosticTrackingService.formatDiagnosticsSummary([DiagnosticFile.new("file:///repo/a.ts", [diag])])
expect(summary).to_contain("a.ts:")
expect(summary).to_contain("[Line 3:5] bad type [TS2322] (ts)")
```

</details>

#### should expose source-backed constants and helpers

- should expose source-backed constants and helpers
- Verify: should expose source-backed constants and helpers
- Pin source surface
   - Expected: err.name equals `DiagnosticsTrackingError`
   - Expected: textBlock("[]") equals `[]`
   - Expected: maxDiagnosticsSummaryChars() equals `4000`
   - Expected: diagnosticTrackingSourceLinesModeled() equals `397`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed constants and helpers")
step("Verify: should expose source-backed constants and helpers")
# @req: REQ-TOOLS-Diag-001
step("Pin source surface")
val err = DiagnosticsTrackingError.new("mismatch")
expect(err.name).to_equal("DiagnosticsTrackingError")
expect(textBlock("[]")).to_equal("[]")
expect(maxDiagnosticsSummaryChars()).to_equal(4000)  # oracle: value fixed by the spec contract
expect(diagnosticTrackingSourceLinesModeled()).to_equal(397)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `N/A - strict llm_caret Claude CLI parity lane.`
- **Plan:** `N/A - target selected from strict checker output.`
- **Design:** `N/A - source mirror for `tmp/claude/claude-code-main/src/services/diagnosticTracking.ts`.`
- **Research:** `N/A - upstream TypeScript file is the source reference.`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Diag-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a36653acd07b936cac7a7f73d678b7ca793d441cd852cdebfe708b7ead17878a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a36653acd07b936cac7a7f73d678b7ca793d441cd852cdebfe708b7ead17878a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a36653acd07b936cac7a7f73d678b7ca793d441cd852cdebfe708b7ead17878a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should initialize once and clear state on shutdown' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should initialize once and clear state on shutdown' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should normalize protocol-prefixed file URIs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should normalize protocol-prefixed file URIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record openFile RPC only when connected' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should record openFile RPC only when connected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should capture baseline and log path mismatch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return only diagnostics not present in baseline' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/diagnosticTracking_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prefer changed _claude_fs_right diagnostics' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
