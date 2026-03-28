# DAP+LSP Tool Chaining for Debug Session Analysis

**Key insight**: DAP gives runtime state (where paused, variable values), LSP gives static knowledge (types, definitions, call graphs). Chain them via **file + line**.

## Tool Summary

### DAP Tools (session-based, JSON)

`debug_create_session`, `debug_set_breakpoint`, `debug_set_function_breakpoint`, `debug_continue`, `debug_step` (over/in/out), `debug_stack_trace`, `debug_get_variables`, `debug_get_source`, `debug_evaluate`, `debug_watch`, `debug_set_variable`, `debug_set_data_breakpoint`, `debug_terminate`

### DAP Log Tools

`debug_log_enable(pattern)`, `debug_log_query(since_id, entry_type)`, `debug_log_tree(format)`, `debug_log_status`

### LSP Tools (file+line, plain text)

`simple_hover`, `simple_definition`, `simple_references`, `simple_type_at`, `simple_workspace_symbols`, `simple_call_hierarchy`, `simple_type_hierarchy`, `simple_implementation`, `simple_context`, `simple_inlay_hints`, `simple_search`

## Bridge: DAP -> LSP

```
debug_stack_trace -> frames[0].source, frames[0].line
                  -> simple_hover(file=..., line=...)
                  -> simple_call_hierarchy(file=..., line=..., direction="incoming")
```

Variable type bridge: `debug_get_variables -> type="LazySession"` -> `simple_workspace_symbols(query="LazySession")` -> `simple_hover(file=..., line=...)`

## Chain Patterns

### 1. Variable -> Type Definition
`debug_get_variables` -> `simple_workspace_symbols(query=type)` -> `simple_hover` at definition

### 2. Frame -> Call Hierarchy
`debug_stack_trace` -> `simple_call_hierarchy(direction="incoming")` to trace callers

### 3. Next-Line Analysis
`debug_stack_trace` -> `debug_get_source(count=20)` -> `simple_hover` + `simple_inlay_hints` on upcoming code

### 4. Runtime Type Narrowing
`debug_get_variables` (concrete type) -> `simple_type_hierarchy(direction="supertypes")` -> `simple_workspace_symbols` for methods

### 5. AOP Log + LSP Cross-Reference
`debug_log_tree` (hot function) -> `simple_search(query=fn)` -> `simple_references` for call sites

## Common Workflows

- **Post-crash**: `stack_trace` -> `get_variables` -> `hover` at crash line -> `definition` on failing expr
- **Call path**: `stack_trace` -> `call_hierarchy(incoming)` per frame -> `get_source` per frame
- **Deep inspect**: `get_variables` -> `workspace_symbols(type)` -> `hover` at def -> `evaluate("var.field")`

## Limitations

- DAP returns paths relative to project root (same as LSP expects)
- DAP frames lack column info -- omit column param for LSP calls
- Limit to 3 LSP calls per debug stop before forming hypothesis
- LSP tools have 30-second timeout
