# LSP & DAP Spec Tests - Language Feature Showcase Plan

**Date:** 2026-01-05
**Purpose:** Create BDD specs for LSP and DAP that demonstrate diverse Simple language features
**Goal:** Each spec showcases different language capabilities while testing functionality

## Overview

Instead of simple procedural tests, we'll write BDD specs that demonstrate:
- Container short grammars (array/dict/tuple literals)
- Attributes and decorators
- Property getters/setters
- Pattern matching
- String interpolation
- Comprehensions
- Async/await
- Error handling with Result types
- Type annotations
- Macros
- And more!

## Feature Distribution Strategy

### LSP Spec Features Map

| Spec Section | Primary Features Showcased |
|--------------|---------------------------|
| **Protocol Basics** | Dict/array short syntax, string interpolation |
| **Message Parsing** | Pattern matching, Result types, enum matching |
| **Document Sync** | Properties (getters/setters), async/await |
| **Diagnostics** | Comprehensions, array methods, error types |
| **Completion** | Attributes/decorators, type annotations |
| **Hover** | Optional types, null coalescing |
| **Definition** | Tuple destructuring, multiple returns |
| **References** | Set operations, LINQ-style queries |
| **Semantic Tokens** | Bitfields, enum flags, bit operations |

### DAP Spec Features Map

| Spec Section | Primary Features Showcased |
|--------------|---------------------------|
| **Protocol Basics** | Tagged unions, variant matching |
| **Initialization** | Builder pattern, method chaining |
| **Breakpoints** | Range expressions, slicing |
| **Stack Traces** | Lazy evaluation, generators |
| **Variables** | Operator overloading, custom indexing |
| **Evaluation** | Macro expansion, compile-time evaluation |
| **Threads** | Actor model, message passing |
| **Launch/Attach** | Resource management (with blocks) |
| **Events** | Observer pattern, event handling |

## Detailed Feature Specifications

### Container Short Grammars

**LSP Example:**
```simple
# Dictionary literal with short syntax
let request = {
    "jsonrpc": "2.0",
    "id": 1,
    "method": "textDocument/didOpen",
    "params": {
        "textDocument": {
            "uri": "file:///test.spl",
            "languageId": "simple",
            "version": 1,
            "text": "fn main():\n    print('hello')"
        }
    }
}

# Array comprehension
let diagnostics = [
    {line: i, message: "Error at line {i}"}
    for i in range(1, 10)
    if errors.contains(i)
]

# Tuple unpacking
let (success, response) = parse_message(data)
```

### Attributes and Decorators

**LSP Example:**
```simple
#[skip("Not implemented yet")]
scenario "LSP handles workspace symbols":
    # Test skipped until feature complete
    pass

#[timeout(5000)]  # 5 second timeout
#[retry(3)]       # Retry up to 3 times
scenario "LSP responds to completion request":
    given server = LspServer.new()
    # ...

#[performance_critical]
#[inline]
fn encode_semantic_tokens(tokens: Array[Token]) -> Array[Int]:
    # Performance-critical token encoding
    pass
```

### Property Getters/Setters

**DAP Example:**
```simple
class DapServer:
    _state: ServerState
    _breakpoints: Dict[String, Array[Breakpoint]]

    # Getter with computed value
    property is_running -> Bool:
        get:
            return self._state == ServerState.Running

    # Setter with validation
    property state -> ServerState:
        get:
            return self._state
        set(value):
            if value == ServerState.Running and not self.initialized:
                raise Error("Cannot run before initialization")
            self._state = value

    # Read-only property
    property breakpoint_count -> Int:
        get:
            return sum(bp.len() for bp in self._breakpoints.values())
```

### Pattern Matching

**LSP Example:**
```simple
fn handle_request(msg: Message) -> Result[Response, Error]:
    match msg:
        case {method: "initialize", params: p}:
            return handle_initialize(p)

        case {method: "textDocument/completion", params: {position: pos, textDocument: doc}}:
            return get_completions(doc, pos)

        case {method: m, id: Some(id)} if m.starts_with("$/"):
            # Ignore notification methods starting with $/
            return Ok(null)

        case {method: unknown}:
            return Err(Error("Unknown method: {unknown}"))
```

### String Interpolation & F-Strings

**DAP Example:**
```simple
fn format_stack_frame(frame: StackFrame) -> String:
    let file = frame.source?.path ?? "<unknown>"
    let line = frame.line
    let func = frame.name

    # String interpolation with expressions
    return "{func} at {file}:{line}"

fn log_breakpoint(bp: Breakpoint):
    # Multi-line interpolated string
    let msg = """
    Breakpoint #{bp.id}
      File: {bp.source}
      Line: {bp.line}
      Condition: {bp.condition ?? "none"}
      Hit count: {bp.hit_count}/{bp.hit_condition ?? "∞"}
    """
    log.debug(msg)
```

### Comprehensions

**LSP Example:**
```simple
# List comprehension with filter
let errors = [
    diag for diag in diagnostics
    if diag.severity == DiagnosticSeverity.Error
]

# Dict comprehension
let symbol_map = {
    sym.name: sym.location
    for sym in document_symbols
}

# Set comprehension
let imported_modules = {
    imp.module_name
    for imp in imports
    if imp.is_valid()
}

# Nested comprehension
let all_tokens = [
    token
    for line in document.lines
    for token in tokenize(line)
]
```

### Async/Await

**LSP Example:**
```simple
async fn handle_completion_request(params: CompletionParams) -> CompletionList:
    # Await document parse
    let document = await parse_document(params.text_document.uri)

    # Await symbol resolution
    let symbols = await resolve_symbols(document)

    # Await type inference
    let types = await infer_types(document, params.position)

    # Parallel awaits
    let (imports, exports) = await [
        analyze_imports(document),
        analyze_exports(document)
    ]

    return generate_completions(symbols, types, imports)
```

### Result Types & Error Handling

**DAP Example:**
```simple
fn set_breakpoint(source: String, line: Int) -> Result[Breakpoint, BreakpointError]:
    # Validate source exists
    let file = File.open(source)?  # Propagate error with ?

    # Validate line number
    if line < 1 or line > file.line_count():
        return Err(BreakpointError.InvalidLine(line))

    # Create breakpoint
    let bp = Breakpoint.new(source, line)

    match self.register_breakpoint(bp):
        case Ok(id):
            bp.id = id
            return Ok(bp)
        case Err(e):
            return Err(BreakpointError.RegistrationFailed(e))
}

# Usage with error handling
scenario "Setting breakpoints":
    given server = DapServer.new()

    when result = server.set_breakpoint("test.spl", 10):
        match result:
            case Ok(bp):
                then bp.id.should_be_greater_than(0)
                and bp.line.should_equal(10)
            case Err(e):
                fail("Unexpected error: {e}")
```

### Type Annotations

**LSP Example:**
```simple
# Generic type parameters
fn find_symbol[T: Symbol](
    symbols: Array[T],
    name: String,
    kind: SymbolKind?
) -> Option[T]:
    for sym in symbols:
        if sym.name == name and (kind is None or sym.kind == kind):
            return Some(sym)
    return None

# Function type annotations
type CompletionProvider = fn(
    document: TextDocument,
    position: Position
) -> Array[CompletionItem]

# Complex type aliases
type ResponseHandler = fn(
    Result[JsonValue, Error]
) -> Promise[Unit]
```

### Macros

**DAP Example:**
```simple
# Macro for generating protocol message types
macro! define_dap_message(name, fields):
    struct {name}:
        @fields

        fn to_json(self) -> JsonValue:
            return {
                "type": "{name}",
                @["{k}": self.{k} for k in @field_names(fields)]
            }

# Usage
define_dap_message!(LaunchRequest, {
    program: String,
    args: Array[String],
    cwd: String?
})

# Generates:
# struct LaunchRequest:
#     program: String
#     args: Array[String]
#     cwd: String?
#     fn to_json(self) -> JsonValue: ...
```

### Operators & Custom Types

**LSP Example:**
```simple
# Custom range type with operator overloading
struct Range:
    start: Position
    end: Position

    # Operator: range contains position
    fn __contains__(self, pos: Position) -> Bool:
        return self.start <= pos and pos <= self.end

    # Operator: range intersection
    fn __and__(self, other: Range) -> Option[Range]:
        let start = max(self.start, other.start)
        let end = min(self.end, other.end)
        if start <= end:
            return Some(Range(start, end))
        return None

# Usage
scenario "Range operations":
    let range1 = Range(Position(0, 0), Position(5, 10))
    let range2 = Range(Position(3, 0), Position(8, 5))

    then Position(2, 5).should_be_in(range1)
    and (range1 & range2).should_equal(Some(Range(Position(3, 0), Position(5, 10))))
```

### Bitfields & Flags

**LSP Example:**
```simple
# Define semantic token types as bitfield
bitfield TokenType: u32:
    Keyword     = 1 << 0
    String      = 1 << 1
    Number      = 1 << 2
    Comment     = 1 << 3
    Function    = 1 << 4
    Variable    = 1 << 5
    Type        = 1 << 6

# Token modifiers as separate bitfield
bitfield TokenModifier: u32:
    Declaration = 1 << 0
    Definition  = 1 << 1
    Readonly    = 1 << 2
    Static      = 1 << 3
    Async       = 1 << 4

# Usage with bit operations
fn encode_token(type: TokenType, modifiers: TokenModifier) -> u32:
    return type | modifiers

scenario "Semantic token encoding":
    let token = encode_token(
        TokenType.Function | TokenType.Keyword,
        TokenModifier.Async | TokenModifier.Declaration
    )

    then token.should_have_flag(TokenType.Function)
    and token.should_have_flag(TokenModifier.Async)
```

### Generators & Lazy Evaluation

**DAP Example:**
```simple
# Generator for stack frames (lazy evaluation)
fn* iterate_stack_frames(thread_id: Int):
    let frame_id = 0
    loop:
        match get_frame(thread_id, frame_id):
            case Some(frame):
                yield frame
                frame_id += 1
            case None:
                break

scenario "Stack trace iteration":
    given server = DapServer.new()
    when frames = iterate_stack_frames(1)

    then frames.take(5).should_have_length(5)
    and frames.filter(|f| f.name.contains("main")).should_exist()
```

### Resource Management (With Blocks)

**DAP Example:**
```simple
# With block for automatic resource cleanup
scenario "Debug session lifecycle":
    with session = DebugSession.new("test.spl"):
        # Session automatically started
        session.set_breakpoint("test.spl", 10)
        session.run()

        # Wait for breakpoint hit
        let event = session.wait_for_event(EventType.Stopped)
        event.reason.should_equal("breakpoint")
    # Session automatically cleaned up and terminated
```

### Tagged Unions

**DAP Example:**
```simple
# Tagged union for different event types
union DapEvent:
    Stopped(reason: String, thread_id: Int)
    Continued(thread_id: Int)
    Thread(reason: String, thread_id: Int)
    Output(category: String, output: String)
    Terminated
    Exited(exit_code: Int)

fn handle_event(event: DapEvent):
    match event:
        case DapEvent.Stopped(reason, tid):
            print("Thread {tid} stopped: {reason}")
        case DapEvent.Output(cat, out):
            print("[{cat}] {out}")
        case DapEvent.Exited(code):
            print("Process exited with code {code}")
        case _:
            print("Other event")
```

## Complete Feature Coverage Matrix

| Feature | LSP Spec | DAP Spec | Section |
|---------|----------|----------|---------|
| Dict/Array literals | ✅ | ✅ | Protocol parsing |
| String interpolation | ✅ | ✅ | Messages, logging |
| Pattern matching | ✅ | ✅ | Request routing, events |
| Async/await | ✅ | ⚠️ | Completion, document sync |
| Result types | ✅ | ✅ | Error handling |
| Properties (get/set) | ⚠️ | ✅ | Server state |
| Comprehensions | ✅ | ⚠️ | Filtering, mapping |
| Attributes | ✅ | ✅ | Test metadata |
| Type annotations | ✅ | ✅ | Function signatures |
| Macros | ⚠️ | ✅ | Protocol messages |
| Operators | ✅ | ⚠️ | Range operations |
| Bitfields | ✅ | ⚠️ | Semantic tokens |
| Generators | ⚠️ | ✅ | Stack iteration |
| With blocks | ⚠️ | ✅ | Resource management |
| Tagged unions | ⚠️ | ✅ | Event types |
| Tuples | ✅ | ✅ | Multiple returns |
| Optional types | ✅ | ✅ | Null safety |
| Enums | ✅ | ✅ | State machines |

✅ = Primary demonstration
⚠️ = Secondary/light usage

## Implementation Strategy

### Phase 1: Create Spec Skeletons
1. Create `simple/std_lib/test/system/tools/lsp_spec.spl`
2. Create `simple/std_lib/test/system/tools/dap_spec.spl`
3. Mark all scenarios as `#[skip]` initially

### Phase 2: Implement LSP Specs
1. Protocol basics (dict/array literals)
2. Message parsing (pattern matching)
3. Document sync (async/await, properties)
4. Diagnostics (comprehensions)
5. Completion (attributes, types)
6. Hover (optionals)
7. Definition (tuples)
8. References (sets, queries)
9. Semantic tokens (bitfields)

### Phase 3: Implement DAP Specs
1. Protocol basics (tagged unions)
2. Initialization (builder pattern)
3. Breakpoints (ranges)
4. Stack traces (generators)
5. Variables (operators)
6. Evaluation (macros)
7. Threads (actors)
8. Launch/attach (with blocks)
9. Events (observers)

### Phase 4: Progressive Un-skip
As features are implemented in LSP/DAP, remove `#[skip]` attributes from corresponding tests.

## Success Criteria

✅ All major Simple language features demonstrated
✅ Each feature used in realistic context
✅ Specs serve as learning examples
✅ Tests are meaningful, not contrived
✅ Code is idiomatic and elegant

## Next Steps

1. Create initial spec files with all features showcased
2. Mark all as `#[skip("Implementation pending")]`
3. Document which scenario demonstrates which feature
4. Progressively implement and un-skip as LSP/DAP develop

Let's build specs that are both test suites AND language showcases! 🚀
