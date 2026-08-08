# lsp_spec

> LSP Server BDD Specification Tests.

<!-- sdn-diagram:id=lsp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

LSP Server BDD Specification Tests.
Validates Language Server Protocol functionality including protocol messages,
positions, ranges, diagnostics, code completion, and document management.

## Scenarios

### LSP Protocol Basics

#### should identify message types with pattern matching

1. expect get message type
2. expect get message type
3. expect get message type


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = LspMessage.Request(1, "initialize")
val notification = LspMessage.Notification("initialized")
val error_msg = LspMessage.Error(404, "Not found")

expect get_message_type(request) == "request"
expect get_message_type(notification) == "notification"
expect get_message_type(error_msg) == "error"
```

</details>

#### should detect error messages

1. expect is error message
2. expect is error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = LspMessage.Request(1, "shutdown")
val error_msg = LspMessage.Error(500, "Server error")

expect is_error_message(request) == false
expect is_error_message(error_msg) == true
```

</details>

#### should extract method from request

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos1 = Position { line: 5, character: 10 }
val pos2 = Position { line: 5, character: 10 }

expect pos1.line == pos2.line
expect pos1.character == pos2.character
```

</details>

#### should validate positions

1. expect is valid position
2. expect is valid position
3. expect is valid position


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid_pos = Position { line: 0, character: 0 }
val invalid_pos1 = Position { line: -1, character: 0 }
val invalid_pos2 = Position { line: 0, character: -5 }

expect is_valid_position(valid_pos) == true
expect is_valid_position(invalid_pos1) == false
expect is_valid_position(invalid_pos2) == false
```

</details>

#### should calculate range length for single line

1. expect range length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range = Range {
    start: Position { line: 5, character: 10 },
    end: Position { line: 5, character: 20 }
}

expect range_length(range) == 10
```

</details>

#### should detect multi-line ranges

1. expect range length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range = Range {
    start: Position { line: 5, character: 10 },
    end: Position { line: 10, character: 5 }
}

expect range_length(range) == -1
```

</details>

### LSP Diagnostics

#### should count error diagnostics

1. expect count errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect count errors
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = []

expect count_errors(diagnostics) == 0
expect len(filter_errors(diagnostics)) == 0
```

</details>

### LSP Code Completion

#### should create keyword completions

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. detail: "fn
2. functions push
3. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. states push
2. states push
3. states push
4. states push
5. states push
6. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. text: "fn main


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. text: "fn main
2. text: "fn main


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect is error message
2. expect is error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val success = LspMessage.Response(1, "OK")
val failure = LspMessage.Error(404, "Not found")

expect is_error_message(success) == false
expect is_error_message(failure) == true
```

</details>

### LSP Data Processing

#### should process array of messages

1. LspMessage Request
2. LspMessage Request
3. LspMessage Notification
4. LspMessage Request


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. LspMessage Request
2. LspMessage Request
3. LspMessage Notification
4. methods push
5. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
