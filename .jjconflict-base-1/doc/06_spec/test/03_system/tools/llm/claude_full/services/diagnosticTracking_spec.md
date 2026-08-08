# Claude Full Diagnostic Tracking

> Checks diagnostic baseline tracking, `_claude_fs_right` preference, path normalization, query lifecycle reset, and human-readable summary formatting for the Claude CLI `diagnosticTracking.ts` parity slice.

<!-- sdn-diagram:id=diagnosticTracking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=diagnosticTracking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

diagnosticTracking_spec -> std
diagnosticTracking_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=diagnosticTracking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Diagnostic Tracking

Checks diagnostic baseline tracking, `_claude_fs_right` preference, path normalization, query lifecycle reset, and human-readable summary formatting for the Claude CLI `diagnosticTracking.ts` parity slice.

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

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

- Initialize and shutdown the service
- service initialize
- service initialize
   - Expected: service.initialized is true
   - Expected: service.mcpConnected is true
- service setBaseline
- service shutdown
   - Expected: service.initialized is false
   - Expected: service.baselineKeys.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize and shutdown the service")
val service = DiagnosticTrackingService.new()
service.initialize(true)
service.initialize(false)
expect(service.initialized).to_equal(true)
expect(service.mcpConnected).to_equal(true)
service.setBaseline("/a", [Diagnostic.new("old", "Error", 0, 0)])
service.shutdown()
expect(service.initialized).to_equal(false)
expect(service.baselineKeys.len()).to_equal(0)
```

</details>

#### should normalize protocol-prefixed file URIs

- Strip file and claude fs prefixes
   - Expected: service.normalizeFileUri("file:///repo/a.ts") equals `/repo/a.ts`
   - Expected: service.normalizeFileUri("_claude_fs_right:/repo/a.ts") equals `/repo/a.ts`
   - Expected: service.normalizeFileUri("_claude_fs_left:/repo/a.ts") equals `/repo/a.ts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Strip file and claude fs prefixes")
val service = DiagnosticTrackingService.new()
expect(service.normalizeFileUri("file:///repo/a.ts")).to_equal("/repo/a.ts")
expect(service.normalizeFileUri("_claude_fs_right:/repo/a.ts")).to_equal("/repo/a.ts")
expect(service.normalizeFileUri("_claude_fs_left:/repo/a.ts")).to_equal("/repo/a.ts")
```

</details>

#### should record openFile RPC only when connected

- Call ensureFileOpened before and after initialization
- service ensureFileOpened
   - Expected: service.rpcLog.len() equals `0`
- service initialize
- service ensureFileOpened


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Call ensureFileOpened before and after initialization")
val service = DiagnosticTrackingService.new()
service.ensureFileOpened("/repo/a.ts")
expect(service.rpcLog.len()).to_equal(0)
service.initialize(true)
service.ensureFileOpened("/repo/a.ts")
expect(service.rpcLog[0]).to_contain("openFile:/repo/a.ts")
```

</details>

#### should capture baseline and log path mismatch

- Capture before edit diagnostics
- service initialize
- service beforeFileEdited
   - Expected: service.getBaseline("/repo/a.ts").len() equals `1`
- service beforeFileEdited


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture before edit diagnostics")
val service = DiagnosticTrackingService.new()
service.initialize(true)
val diag = Diagnostic.new("old", "Error", 0, 0)
service.beforeFileEdited("/repo/a.ts", [DiagnosticFile.new("file:///repo/a.ts", [diag])], 42)
expect(service.getBaseline("/repo/a.ts").len()).to_equal(1)
service.beforeFileEdited("/repo/b.ts", [DiagnosticFile.new("file:///repo/a.ts", [diag])], 43)
expect(service.errors[0]).to_contain("Diagnostics file path mismatch")
```

</details>

#### should return only diagnostics not present in baseline

- Compare current diagnostics with baseline
- service initialize
- service setBaseline
   - Expected: result.len() equals `1`
   - Expected: result[0].diagnostics[0].message equals `new`
   - Expected: service.getBaseline("/repo/a.ts").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare current diagnostics with baseline")
val service = DiagnosticTrackingService.new()
service.initialize(true)
val old = Diagnostic.new("old", "Warning", 0, 0)
val newDiag = Diagnostic.new("new", "Error", 1, 2)
service.setBaseline("/repo/a.ts", [old])
val result = service.getNewDiagnostics([DiagnosticFile.new("file:///repo/a.ts", [old, newDiag])])
expect(result.len()).to_equal(1)
expect(result[0].diagnostics[0].message).to_equal("new")
expect(service.getBaseline("/repo/a.ts").len()).to_equal(2)
```

</details>

#### should prefer changed _claude_fs_right diagnostics

- Use right-file diagnostics when first seen
- service initialize
- service setBaseline
- DiagnosticFile new
- DiagnosticFile new
   - Expected: result[0].diagnostics[0].message equals `right`
   - Expected: service.getRight("/repo/a.ts").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(service.getRight("/repo/a.ts").len()).to_equal(1)
```

</details>

#### should compare diagnostic arrays independent of order

- Compare equal arrays in different order
   - Expected: service.areDiagnosticArraysEqual([a, b], [b, a]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare equal arrays in different order")
val service = DiagnosticTrackingService.new()
val a = Diagnostic.new("a", "Error", 0, 0)
val b = Diagnostic.new("b", "Hint", 1, 1)
expect(service.areDiagnosticArraysEqual([a, b], [b, a])).to_equal(true)
```

</details>

#### should reset on query start after initialization

- Initialize then start a new query
- service handleQueryStart
- service setBaseline
- service handleQueryStart
   - Expected: service.initialized is true
   - Expected: service.baselineKeys.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize then start a new query")
val service = DiagnosticTrackingService.new()
service.handleQueryStart(true)
service.setBaseline("/repo/a.ts", [Diagnostic.new("old", "Info", 0, 0)])
service.handleQueryStart(true)
expect(service.initialized).to_equal(true)
expect(service.baselineKeys.len()).to_equal(0)
```

</details>

#### should format diagnostics summary with symbols, code, and source

- Format a diagnostic file
- var diag = Diagnostic new


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Pin source surface
   - Expected: err.name equals `DiagnosticsTrackingError`
   - Expected: textBlock("[]") equals `[]`
   - Expected: maxDiagnosticsSummaryChars() equals `4000`
   - Expected: diagnosticTrackingSourceLinesModeled() equals `397`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source surface")
val err = DiagnosticsTrackingError.new("mismatch")
expect(err.name).to_equal("DiagnosticsTrackingError")
expect(textBlock("[]")).to_equal("[]")
expect(maxDiagnosticsSummaryChars()).to_equal(4000)
expect(diagnosticTrackingSourceLinesModeled()).to_equal(397)
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

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for `tmp/claude/claude-code-main/src/services/diagnosticTracking.ts`.](N/A - source mirror for `tmp/claude/claude-code-main/src/services/diagnosticTracking.ts`.)
- **Research:** [N/A - upstream TypeScript file is the source reference.](N/A - upstream TypeScript file is the source reference.)


</details>
