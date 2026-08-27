# lsp_spec

> LSP Server BDD Specification Tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lsp_spec

LSP Server BDD Specification Tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | LSP |
| Status | Active |
| Source | `test/03_system/tools/lsp/lsp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

LSP Server BDD Specification Tests.
Validates Language Server Protocol functionality including protocol messages,
positions, ranges, diagnostics, code completion, and document management.

## Scenarios

### LSP Protocol Basics

#### should identify message types with pattern matching

- should identify message types with pattern matching


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should identify message types with pattern matching")
val request = LspMessage.Request(1, "initialize")
val notification = LspMessage.Notification("initialized")
val error_msg = LspMessage.Error(404, "Not found")

expect get_message_type(request) == "request"
expect get_message_type(notification) == "notification"
expect get_message_type(error_msg) == "error"
```

</details>

#### should detect error messages

- should detect error messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect error messages")
val request = LspMessage.Request(1, "shutdown")
val error_msg = LspMessage.Error(500, "Server error")

expect is_error_message(request) == false
expect is_error_message(error_msg) == true
```

</details>

#### should extract method from request

- should extract method from request


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should extract method from request")
val msg = LspMessage.Request(5, "textDocument/completion")

match msg:
    case LspMessage.Request(id, method):
        expect method == "textDocument/completion"
        expect id == 5
    _:
        fail "Should be a request"
```

</details>

### LSP Position and Range

#### should create and compare positions

- should create and compare positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create and compare positions")
val pos1 = Position { line: 5, character: 10 }
val pos2 = Position { line: 5, character: 10 }

expect pos1.line == pos2.line
expect pos1.character == pos2.character
```

</details>

#### should validate positions

- should validate positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate positions")
val valid_pos = Position { line: 0, character: 0 }
val invalid_pos1 = Position { line: -1, character: 0 }
val invalid_pos2 = Position { line: 0, character: -5 }

expect is_valid_position(valid_pos) == true
expect is_valid_position(invalid_pos1) == false
expect is_valid_position(invalid_pos2) == false
```

</details>

#### should calculate range length for single line

- should calculate range length for single line


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should calculate range length for single line")
val range = Range {
    start: Position { line: 5, character: 10 },
    end: Position { line: 5, character: 20 }
}

expect range_length(range) == 10
```

</details>

#### should detect multi-line ranges

- should detect multi-line ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect multi-line ranges")
val range = Range {
    start: Position { line: 5, character: 10 },
    end: Position { line: 10, character: 5 }
}

expect range_length(range) == -1
```

</details>

### LSP Diagnostics

#### should count error diagnostics

- should count error diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should count error diagnostics")
val diagnostics = [
    Diagnostic {
        range: Range { start: Position { line: 0, character: 0 }, end: Position { line: 0, character: 5 } },
        severity: DiagnosticSeverity.Error,
        message: "Undefined variable",
        source: "simple"
    },
    Diagnostic {
        range: Range { start: Position { line: 1, character: 0 }, end: Position { line: 1, character: 10 } },
        severity: DiagnosticSeverity.Warning,
        message: "Unused variable",
        source: "simple"
    },
    Diagnostic {
        range: Range { start: Position { line: 2, character: 0 }, end: Position { line: 2, character: 8 } },
        severity: DiagnosticSeverity.Error,
        message: "Type mismatch",
        source: "simple"
    }
]

expect count_errors(diagnostics) == 2
```

</details>

#### should filter error diagnostics

- should filter error diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should filter error diagnostics")
val diagnostics = [
    Diagnostic {
        range: Range { start: Position { line: 0, character: 0 }, end: Position { line: 0, character: 5 } },
        severity: DiagnosticSeverity.Error,
        message: "Error 1",
        source: "simple"
    },
    Diagnostic {
        range: Range { start: Position { line: 1, character: 0 }, end: Position { line: 1, character: 10 } },
        severity: DiagnosticSeverity.Warning,
        message: "Warning 1",
        source: "simple"
    }
]

val errors = filter_errors(diagnostics)
expect len(errors) == 1
expect errors[0].severity == DiagnosticSeverity.Error
```

</details>

#### should handle empty diagnostic list

- should handle empty diagnostic list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle empty diagnostic list")
val diagnostics = []

expect count_errors(diagnostics) == 0
expect len(filter_errors(diagnostics)) == 0
```

</details>

### LSP Code Completion

#### should create keyword completions

- should create keyword completions


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create keyword completions")
val keywords = [
    CompletionItem {
        label: "fn",
        kind: CompletionItemKind.Keyword,
        detail: "Function definition",
        documentation: "Define a new function"
    },
    CompletionItem {
        label: "class",
        kind: CompletionItemKind.Keyword,
        detail: "Class definition",
        documentation: "Define a new class"
    },
    CompletionItem {
        label: "if",
        kind: CompletionItemKind.Keyword,
        detail: "Conditional statement",
        documentation: "Conditional execution"
    }
]

expect len(keywords) == 3
expect keywords[0].label == "fn"
expect keywords[0].kind == CompletionItemKind.Keyword
```

</details>

#### should filter completions by kind

- should filter completions by kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should filter completions by kind")
val items = [
    CompletionItem {
        label: "my_function",
        kind: CompletionItemKind.Function,
        detail: "fn() -> i64",
        documentation: "My function"
    },
    CompletionItem {
        label: "my_variable",
        kind: CompletionItemKind.Variable,
        detail: "i64",
        documentation: "My variable"
    },
    CompletionItem {
        label: "MyClass",
        kind: CompletionItemKind.Class,
        detail: "class",
        documentation: "My class"
    }
]

var functions = []
for item in items:
    if item.kind == CompletionItemKind.Function:
        functions.push(item)

expect len(functions) == 1
expect functions[0].label == "my_function"
```

</details>

### LSP Server State

#### should transition from Uninitialized to Initializing

- should transition from Uninitialized to Initializing


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should transition from Uninitialized to Initializing")
var state = ServerState.Uninitialized

# Simulate state transition
state = ServerState.Initializing

match state:
    case ServerState.Initializing:
        expect true
    _:
        fail "Should be Initializing"
```

</details>

#### should track server lifecycle

- should track server lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should track server lifecycle")
var states = []

states.push(ServerState.Uninitialized)
states.push(ServerState.Initializing)
states.push(ServerState.Running)
states.push(ServerState.ShuttingDown)
states.push(ServerState.Stopped)

expect len(states) == 5
```

</details>

### LSP Document Management

#### should create text document

- should create text document


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create text document")
val doc = TextDocument {
    uri: "file:///test.spl",
    language_id: "simple",
    version: 1,
    text: "fn main():{NL}    print('hello')"
}

expect doc.uri == "file:///test.spl"
expect doc.language_id == "simple"
expect doc.version == 1
```

</details>

#### should track document versions

- should track document versions


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should track document versions")
val doc_v1 = TextDocument {
    uri: "file:///test.spl",
    language_id: "simple",
    version: 1,
    text: "fn main(): pass"
}

# Simulate version update by creating new document
val doc_v2 = TextDocument {
    uri: "file:///test.spl",
    language_id: "simple",
    version: 2,
    text: "fn main(): pass"
}

expect doc_v1.version == 1
expect doc_v2.version == 2
```

</details>

### LSP Error Handling

#### should handle parse errors with enum

- should handle parse errors with enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle parse errors with enum")
val error = LspMessage.Error(-32700, "Parse error")

match error:
    case LspMessage.Error(code, msg):
        expect code == -32700
        expect msg == "Parse error"
    _:
        fail "Should be an error message"
```

</details>

#### should distinguish between error and success

- should distinguish between error and success


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should distinguish between error and success")
val success = LspMessage.Response(1, "OK")
val failure = LspMessage.Error(404, "Not found")

expect is_error_message(success) == false
expect is_error_message(failure) == true
```

</details>

### LSP Data Processing

#### should process array of messages

- should process array of messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should process array of messages")
val messages = [
    LspMessage.Request(1, "initialize"),
    LspMessage.Request(2, "shutdown"),
    LspMessage.Notification("exit")
]

var request_count = 0
for msg in messages:
    val is_request = match msg:
        LspMessage.Request(_, _): true
        _: false
    if is_request:
        request_count = request_count + 1

expect request_count == 2
```

</details>

#### should collect method names from requests

- should collect method names from requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should collect method names from requests")
val messages = [
    LspMessage.Request(1, "initialize"),
    LspMessage.Request(2, "textDocument/hover"),
    LspMessage.Notification("initialized")
]

var methods = []
for msg in messages:
    val method = get_method_name(msg)
    methods.push(method)

expect len(methods) == 3
expect methods[0] == "initialize"
expect methods[1] == "textDocument/hover"
expect methods[2] == "initialized"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `8dffde7ba7c94702f39110ea9724ccf0061686bb4096a50e86a12243231c750c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8dffde7ba7c94702f39110ea9724ccf0061686bb4096a50e86a12243231c750c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8dffde7ba7c94702f39110ea9724ccf0061686bb4096a50e86a12243231c750c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/lsp/lsp_spec.spl
mirror: doc/06_spec/03_system/tools/lsp/lsp_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/lsp/lsp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/lsp/lsp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/lsp/lsp_spec.spl:184:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should identify message types with pattern matching' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/lsp/lsp_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should identify message types with pattern matching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/lsp/lsp_spec.spl:196:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should detect error messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/lsp/lsp_spec.spl:196:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should detect error messages' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/lsp/lsp_spec.spl:206:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract method from request' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/lsp/lsp_spec.spl:206:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should extract method from request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/lsp/lsp_spec.spl:226:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create and compare positions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/lsp/lsp_spec.spl:236:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate positions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/lsp/lsp_spec.spl:248:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should calculate range length for single line' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
