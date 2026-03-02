# DAP+LSP Tool Chaining for Debug Session Analysis

**Use when:** Enriching active debug sessions with static analysis. The key insight: DAP tools give you runtime state (where paused, variable values), LSP tools give you static knowledge (types, definitions, call graphs). Chain them together for deep understanding.

## Tool Inventory

### DAP Tools (session-based, return JSON)

| Tool | Key Params | Key Output Fields |
|------|-----------|-------------------|
| `debug_create_session` | `program`, `target_type` | `session_id`, `state` |
| `debug_set_breakpoint` | `session_id`, `file`, `line` | `breakpoint_id`, `verified` |
| `debug_set_function_breakpoint` | `session_id`, `function_name` | `breakpoint_id` |
| `debug_continue` | `session_id` | `state` ("running") |
| `debug_step` | `session_id`, `mode` (over/in/out) | `state` ("paused") |
| `debug_stack_trace` | `session_id` | `frames[].source`, `frames[].line`, `frames[].name` |
| `debug_get_variables` | `session_id` | `variables[]` (name, value, type) |
| `debug_get_source` | `session_id`, `file`, `start_line`, `count` | `source` (numbered lines) |
| `debug_evaluate` | `session_id`, `expression` | `result`, `type` |
| `debug_watch` | `session_id`, `action` (add/remove/list) | `watches[]` |
| `debug_set_variable` | `session_id`, `name`, `value` | `success`, `data_breakpoint_hit` |
| `debug_set_data_breakpoint` | `session_id`, `name`, `access_type` | `breakpoint_id` |
| `debug_terminate` | `session_id` | `state` ("terminated") |

### DAP Log Tools (cross-session tracing)

| Tool | Key Params | Key Output Fields |
|------|-----------|-------------------|
| `debug_log_enable` | `pattern` (default `*`) | `status` |
| `debug_log_query` | `since_id`, `entry_type` | `entries[]` (id, entry_type, function_name, message) |
| `debug_log_tree` | `format` (text/json) | `tree` (hierarchical call trace) |
| `debug_log_status` | — | `enabled`, `entry_count` |

### LSP Tools (file+line based, return plain text)

| Tool | Key Params | Purpose |
|------|-----------|---------|
| `simple_hover` | `file`, `line`, `column` | Type + docs at position |
| `simple_definition` | `file`, `line`, `column` | Go-to-definition |
| `simple_references` | `file`, `line`, `column` | Find all references |
| `simple_type_at` | `file`, `line`, `column` | Type info at position |
| `simple_type_definition` | `file`, `line`, `column` | Where a type is defined |
| `simple_workspace_symbols` | `query`, `kind` | Search symbols project-wide |
| `simple_call_hierarchy` | `file`, `line`, `direction` | Incoming/outgoing calls |
| `simple_type_hierarchy` | `file`, `line`, `direction` | Super/sub type relationships |
| `simple_implementation` | `file`, `line` | Find trait implementations |
| `simple_context` | `file`, `target` | Full module context pack |
| `simple_inlay_hints` | `file`, `start_line`, `end_line` | Inline type annotations |
| `simple_search` | `query`, `kind`, `scope` | Language-aware code search |

## The Bridge: DAP Output → LSP Input

The fundamental connection between DAP and LSP is **file + line**:

```
debug_stack_trace → frames[0].source = "src/compiler/10.frontend/core/parser.spl"
                  → frames[0].line   = 42
                  → frames[0].name   = "parse_expr"
                                ↓
simple_hover(file="src/compiler/10.frontend/core/parser.spl", line="42")
simple_call_hierarchy(file=..., line="42", direction="incoming")
simple_references(file=..., line="42")
```

**Variable type bridge:**
```
debug_get_variables → variable.type = "LazySession"
                                ↓
simple_workspace_symbols(query="LazySession", kind="struct")
  → returns file + line where LazySession is defined
                                ↓
simple_hover(file=..., line=...)
  → returns full type definition + docs
```

## Output Format Reference

**DAP tools** return JSON wrapped in MCP result text. Extract fields by reading the JSON structure:
```json
{"session_id": "session_1", "frames": [{"id": 0, "name": "main", "source": "file.spl", "line": 1}]}
```

**LSP tools** return plain text with a header line:
```
-- simple_hover (exit: 0) --
fn parse_expr(tokens: List<Token>) -> Expr
  Parse an expression from the token stream.
  Returns: Expr node
```

The `exit: 0` means success. Non-zero means the query failed (file not found, position invalid, etc.).

## Type Normalization

DAP variable types may use different conventions than LSP:
- DAP says `Int`, `i64`, `int` → all mean the same built-in type
- DAP says `text`, `Text`, `string` → all mean the built-in text type
- **Capital letter + no spaces = user-defined type** → pass as-is to `simple_workspace_symbols`
- Examples: `LazySession`, `LazyBreakpoint`, `Token`, `Expr` → search directly

## Chain Pattern 1: Variable → Type Definition

**Goal:** Understand what a runtime variable actually is by finding its type definition.

```
Step 1: debug_get_variables(session_id)
        → variable: {name: "session", type: "LazySession", value: "..."}

Step 2: simple_workspace_symbols(query="LazySession", kind="struct")
        → src/app/mcp/main_lazy_json.spl:15 — struct LazySession

Step 3: simple_hover(file="src/app/mcp/main_lazy_json.spl", line="15")
        → Full struct definition with all fields and docs
```

**When to use:** Any time you see an unfamiliar type in the variables pane.

## Chain Pattern 2: Frame → Call Hierarchy

**Goal:** Understand why execution reached this point by tracing the call chain.

```
Step 1: debug_stack_trace(session_id)
        → frame[0]: {name: "handle_debug_step", source: "main_lazy_debug_tools.spl", line: 179}

Step 2: simple_call_hierarchy(
            file="src/app/mcp/main_lazy_debug_tools.spl",
            line="179",
            direction="incoming"
        )
        → Shows all callers of handle_debug_step

Step 3: simple_call_hierarchy(..., direction="outgoing")
        → Shows all functions handle_debug_step calls
```

**When to use:** "Why did we end up here?" — trace the call path.

## Chain Pattern 3: Next-Line Analysis

**Goal:** Understand what's about to execute before stepping.

```
Step 1: debug_stack_trace(session_id)
        → paused at line 42

Step 2: debug_get_source(session_id, file="...", start_line="42", count="20")
        → see the next 20 lines of source

Step 3: simple_hover(file="...", line="45")
        → type info for a function call on line 45

Step 4: simple_inlay_hints(file="...", start_line="42", end_line="62")
        → see inferred types for all expressions in the range
```

**When to use:** Before deciding whether to step-over or step-into.

## Chain Pattern 4: Runtime Type Narrowing

**Goal:** When the runtime type differs from the declared type, find the concrete implementation.

```
Step 1: debug_get_variables(session_id)
        → variable: {name: "backend", type: "CBackend"}
        (but the parameter was declared as trait Codegen)

Step 2: simple_type_hierarchy(
            file="src/compiler/70.backend/backend/c_backend.spl",
            line="1",
            direction="supertypes"
        )
        → shows CBackend implements Codegen trait

Step 3: simple_workspace_symbols(query="CBackend")
        → find all CBackend methods and fields
```

**When to use:** Polymorphic dispatch — the variable's declared type is a trait but runtime is concrete.

## Chain Pattern 5: AOP Log + LSP Cross-Reference

**Goal:** Find hot paths from debug logs, then understand their full context.

```
Step 1: debug_log_enable(pattern="*")
        ... run program ...
        debug_log_tree(format="text")
        → identifies hot function: "eval_call" called 500 times

Step 2: simple_search(query="eval_call", kind="fn")
        → src/compiler/10.frontend/core/interpreter/eval.spl:234

Step 3: simple_references(file="...", line="234")
        → find all call sites of eval_call

Step 4: simple_context(file="src/compiler/10.frontend/core/interpreter/eval.spl")
        → full module context: imports, symbols, diagnostics
```

**When to use:** Performance investigation — find what's hot, then understand why.

## Common Workflows

### "What went wrong?" (Post-crash analysis)

1. `debug_stack_trace` → identify crash location (file + line)
2. `debug_get_variables` → inspect local state at crash point
3. `simple_hover` at crash line → understand types involved
4. `simple_definition` on the failing expression → find source of bad value
5. Form hypothesis, set conditional breakpoint, reproduce

### "Why did we land here?" (Call path investigation)

1. `debug_stack_trace` → get all frames
2. For each frame: `simple_call_hierarchy(direction="incoming")` → trace callers
3. `debug_get_source` on each frame → read the calling code
4. Walk up the stack correlating runtime values with static call graph

### "What does this variable contain?" (Deep inspect)

1. `debug_get_variables` → get variable name + type
2. If user-defined type: `simple_workspace_symbols(query=type_name)` → find definition
3. `simple_hover` at definition → read field list
4. `debug_evaluate(expression="variable.field")` → inspect specific fields
5. For nested types: repeat from step 2

## Limitations

- **Stub server:** The current MCP debug server is stateful but lightweight — `debug_get_variables` returns empty arrays, `debug_stack_trace` returns a single synthetic frame pointing to the program entry. Real variable inspection requires a connected runtime.
- **LSP timeout:** All `simple_*` tools have a 30-second timeout. Complex queries on large files may time out.
- **Chain depth:** Limit yourself to 3 LSP calls per debug stop before forming a hypothesis. More than that means you need to narrow your question.
- **File paths:** DAP returns paths relative to project root (e.g., `src/app/mcp/main.spl`). LSP tools expect the same format. No path conversion needed.
- **Column precision:** DAP frames don't include column info. When calling LSP tools from DAP output, omit the `column` parameter — most LSP tools work with just file + line.
