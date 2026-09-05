# Lsp Specification

> Tests covering LSP - initialization, LSP - text synchronization, LSP - code completion, LSP - hover information, LSP - go to definition, LSP - diagnostics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Specification

## Scenarios

### LSP - initialization

#### handles initialize request

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- handles initialize request


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles initialize request")
# LSP initialize request
val capabilities = {
    "textDocument": {
        "completion": {"dynamicRegistration": true},
        "hover": {"dynamicRegistration": true}
    }
}

expect capabilities.has("textDocument")
```

</details>

#### responds with server capabilities

- responds with server capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("responds with server capabilities")
val server_capabilities = {
    "completionProvider": true,
    "hoverProvider": true,
    "definitionProvider": true
}

expect server_capabilities["completionProvider"]
```

</details>

### LSP - text synchronization

#### handles didOpen notification

- handles didOpen notification


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles didOpen notification")
val doc = {
    "uri": "file:///test.spl",
    "languageId": "simple",
    "version": 1,
    "text": "val x = 42"
}

expect doc["languageId"] == "simple"
```

</details>

#### handles didChange notification

- handles didChange notification


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles didChange notification")
val changes = [
    {"text": "val y = 10"}
]

expect changes.len() == 1
```

</details>

#### handles didClose notification

- handles didClose notification


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles didClose notification")
val uri = "file:///test.spl"
expect uri.starts_with("file://")
```

</details>

### LSP - code completion

#### provides keyword completions

- provides keyword completions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides keyword completions")
val keywords = ["fn", "class", "struct", "enum", "val", "var"]
expect keywords.contains("fn")
expect keywords.contains("val")
```

</details>

#### provides variable completions

- provides variable completions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides variable completions")
# In scope: val x = 42
val completions = ["x"]
expect completions.contains("x")
```

</details>

#### provides method completions

- provides method completions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides method completions")
# obj.method_name
val methods = ["len", "is_empty", "contains"]
expect methods.len() > 0
```

</details>

### LSP - hover information

#### shows type information on hover

- shows type information on hover


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows type information on hover")
# Hovering over 'x' in 'val x: i64 = 42'
val hover_info = "i64"
expect hover_info.len() > 0
```

</details>

#### shows documentation on hover

- shows documentation on hover


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows documentation on hover")
# Hovering over function with docstring
val doc = "Returns the length of the string"
expect doc.contains("length")
```

</details>

### LSP - go to definition

#### finds function definitions

- finds function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds function definitions")
# Jump from call site to definition
val location = {"uri": "file:///test.spl", "line": 10}
expect location.has("uri")
```

</details>

#### finds variable definitions

- finds variable definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds variable definitions")
# Jump from usage to declaration
val location = {"uri": "file:///test.spl", "line": 5}
expect location["line"] == 5
```

</details>

### LSP - diagnostics

#### reports syntax errors

- reports syntax errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports syntax errors")
# Missing colon on function def
val diagnostic = {
    "severity": "error",
    "message": "Expected ':' after function signature"
}

expect diagnostic["severity"] == "error"
```

</details>

#### reports type errors

- reports type errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports type errors")
# Type mismatch
val diagnostic = {
    "severity": "error",
    "message": "Type mismatch: expected i64, got text"
}

expect diagnostic["message"].contains("Type mismatch")
```

</details>

#### reports warnings

- reports warnings


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports warnings")
# Unused variable
val diagnostic = {
    "severity": "warning",
    "message": "Unused variable 'x'"
}

expect diagnostic["severity"] == "warning"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LSP - initialization, LSP - text synchronization, LSP - code completion, LSP - hover information, LSP - go to definition, LSP - diagnostics.
- LSP - initialization
- LSP - text synchronization
- LSP - code completion
- LSP - hover information
- LSP - go to definition
- LSP - diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a5b98ae6a2390819fd5ba2a6fc00987ba77387e4d570219c0d5bf323b6fb682d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5b98ae6a2390819fd5ba2a6fc00987ba77387e4d570219c0d5bf323b6fb682d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5b98ae6a2390819fd5ba2a6fc00987ba77387e4d570219c0d5bf323b6fb682d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp_spec.spl
mirror: doc/06_spec/unit/app/lsp_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles initialize request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'responds with server capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles didOpen notification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
