# Interpreter Hooks API Guide

**Location**: `src/runtime/hooks.spl`
**Purpose**: Provide debugging integration (DAP) with interpreter execution control
**Status**: Phase 1 - API Design Complete ✅

---

## Overview

The Interpreter Hooks API provides a high-level interface for debuggers to control program execution, inspect state, and receive debug events. It's designed to support Debug Adapter Protocol (DAP) features like:

- Breakpoint management (line, conditional, function, log points)
- Step execution (over, into, out)
- Stack frame inspection
- Variable inspection
- Expression evaluation in debug context

## Architecture

```
┌─────────────────────────────────────┐
│    DAP Server (dap/server.spl)      │
│  (setBreakpoints, stackTrace, etc.) │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│  Interpreter Hooks API (hooks.spl)  │
│  - InterpreterHookContext           │
│  - Breakpoint management            │
│  - Execution control                │
└──────────────┬──────────────────────┘
               │
               ▼
┌─────────────────────────────────────┐
│     Interpreter Internal            │
│  - Bytecode execution               │
│  - Stack frame management           │
│  - Variable storage                 │
└─────────────────────────────────────┘
```

## Core Concepts

### 1. InterpreterHookContext

The main entry point for debugging operations. Maintains breakpoints and execution state.

```simple
import runtime.hooks

# Create hook context
val hook_ctx = InterpreterHookContext.create()

# Enable debugging
hook_ctx.enable()

# Add breakpoint
val bp_id = hook_ctx.add_breakpoint("src/main.spl", 42)

# Continue execution
hook_ctx.continue()

# Get stack frames when paused
val frames = hook_ctx.stack_frames()
```

### 2. Execution States

```simple
enum ExecutionState:
    Running    # Program is executing
    Paused     # Paused at breakpoint or step
    Stopped    # Terminated (error or exit)
    Completed  # Finished normally
```

### 3. Event-Driven Model

Debug events are sent to the debugger via callbacks:

```simple
hook_ctx.set_event_callback(\event:
    match event:
        DebugEvent.Breakpoint(id):
            print "Hit breakpoint {id.id}"
        DebugEvent.Step:
            print "Step completed"
        DebugEvent.Exception(message):
            print "Exception: {message}"
        DebugEvent.Output(message):
            print "Output: {message}"
        DebugEvent.Exit(exit_code):
            print "Program exited with code {exit_code}"
)
```

## API Reference

### Context Creation

```simple
# Create a new hook context
static fn InterpreterHookContext.create() -> InterpreterHookContext

# Enable/disable debugging
me hook_ctx.enable()
me hook_ctx.disable()
```

### Breakpoint Management

#### Line Breakpoints

```simple
# Add a simple line breakpoint
me hook_ctx.add_breakpoint(file: text, line: i64) -> BreakpointID
```

#### Conditional Breakpoints

```simple
# Add a conditional breakpoint
val bp_id = hook_ctx.add_breakpoint_with_options(
    file: "src/main.spl",
    line: 42,
    condition: Some("x > 10"),
    hit_condition: None,
    log_message: None,
)
```

#### Hit Conditions

Hit conditions control when a breakpoint triggers based on hit count:

```simple
# Break when hit count >= 5
val bp_id = hook_ctx.add_breakpoint_with_options(
    file: "src/main.spl",
    line: 42,
    condition: None,
    hit_condition: Some(">= 5"),
    log_message: None,
)

# Break on every 2nd hit
val bp_id = hook_ctx.add_breakpoint_with_options(
    file: "src/main.spl",
    line: 42,
    condition: None,
    hit_condition: Some("% 2 == 0"),
    log_message: None,
)
```

**Supported operators**:
- `>= N` - Hit count greater than or equal to N
- `<= N` - Hit count less than or equal to N
- `> N` - Hit count greater than N
- `< N` - Hit count less than N
- `== N` - Hit count equals N
- `% N == M` - Hit count modulo N equals M

#### Log Points

Log points print a message without stopping execution:

```simple
# Add a log point
val bp_id = hook_ctx.add_breakpoint_with_options(
    file: "src/main.spl",
    line: 42,
    condition: None,
    hit_condition: None,
    log_message: Some("Variable x = {x}, y = {y}"),
)
```

Variables in `{braces}` are interpolated with current values.

#### Breakpoint Control

```simple
# Remove a breakpoint
me hook_ctx.remove_breakpoint(id: BreakpointID)

# Enable/disable a breakpoint
me hook_ctx.set_breakpoint_enabled(id: BreakpointID, enabled: bool)

# Get all breakpoints
fn hook_ctx.get_breakpoints() -> [Breakpoint]
```

### Execution Control

```simple
# Continue execution
me hook_ctx.continue() -> ExecutionState

# Pause execution
me hook_ctx.pause()

# Step over (don't enter function calls)
me hook_ctx.step_over() -> ExecutionState

# Step into (enter function calls)
me hook_ctx.step_into() -> ExecutionState

# Step out (execute until current function returns)
me hook_ctx.step_out() -> ExecutionState

# Terminate execution
me hook_ctx.terminate()
```

### Stack Inspection

```simple
# Get current stack frames (only when paused)
me hook_ctx.stack_frames() -> [StackFrame]

# Get a specific frame
fn hook_ctx.get_frame(frame_id: i64) -> Option<StackFrame>
```

**StackFrame structure**:
```simple
struct StackFrame:
    id: i64          # Frame ID (0 = current, 1 = caller, etc.)
    name: text       # Function/method name
    file: text       # Source file
    line: i64        # Current line
    column: i64      # Current column
    scope_id: i64    # Scope ID for variable lookup
```

### Variable Inspection

```simple
# Get variables in a specific scope
fn hook_ctx.variables_in_scope(frame_id: i64, scope: VariableScope) -> [Variable]

# Get all variables in a frame
fn hook_ctx.variables_in_frame(frame_id: i64) -> [Variable]

# Get a specific variable by name
fn hook_ctx.get_variable(frame_id: i64, name: text) -> Option<Variable>
```

**Variable scopes**:
```simple
enum VariableScope:
    Local      # Local variables in current frame
    Global     # Global/module-level variables
    Closure    # Captured closure variables
    Argument   # Function arguments
```

**Variable structure**:
```simple
struct Variable:
    name: text
    value: text            # String representation
    type: text             # Type name
    scope: VariableScope
    is_mutable: bool
    memory_address: Option<i64>  # For advanced inspection
```

### Expression Evaluation

```simple
# Evaluate an expression in the context of a frame
fn hook_ctx.evaluate(expr: text, frame_id: i64) -> EvalResult
```

**Example**:
```simple
# When paused, evaluate expression
val result = hook_ctx.evaluate("x + y * 2", frame_id: 0)

if result.error.?:
    print "Eval error: {result.error.unwrap()}"
else:
    print "Result: {result.value} (type: {result.type})"
```

## Integration with DAP

Example DAP server integration:

```simple
import runtime.hooks
import app.dap.protocol

class SimpleDAP:
    hook_ctx: InterpreterHookContext

    fn handle_set_breakpoints(params: SetBreakpointsArguments) -> [Breakpoint]:
        val file = params.source.path

        # Clear existing breakpoints for file
        # ... (remove old breakpoints) ...

        # Add new breakpoints
        var result = []
        for bp_request in params.breakpoints:
            val bp_id = self.hook_ctx.add_breakpoint_with_options(
                file: file,
                line: bp_request.line,
                condition: bp_request.condition,
                hit_condition: bp_request.hitCondition,
                log_message: bp_request.logMessage,
            )

            result.push(Breakpoint(
                id: bp_id.id,
                verified: true,
                line: bp_request.line,
            ))

        result

    fn handle_continue(params: ContinueArguments):
        self.hook_ctx.continue()

    fn handle_stack_trace(params: StackTraceArguments) -> [StackFrame]:
        self.hook_ctx.stack_frames()

    fn handle_scopes(params: ScopesArguments) -> [Scope]:
        # Get variables for frame
        val vars = self.hook_ctx.variables_in_frame(params.frameId)

        # Group by scope
        [
            Scope(name: "Locals", variablesReference: 1, expensive: false),
            Scope(name: "Arguments", variablesReference: 2, expensive: false),
            Scope(name: "Globals", variablesReference: 3, expensive: false),
        ]

    fn handle_variables(params: VariablesArguments) -> [Variable]:
        val scope = match params.variablesReference:
            1: VariableScope.Local
            2: VariableScope.Argument
            3: VariableScope.Global
            _: return []

        self.hook_ctx.variables_in_scope(params.frameId, scope)
```

## FFI Integration

The hooks API relies on FFI functions implemented in Rust:

### Required FFI Functions

```simple
# Breakpoint management
extern fn rt_hook_add_breakpoint(file: text, line: i64, id: i64)
extern fn rt_hook_remove_breakpoint(file: text, line: i64)
extern fn rt_hook_set_breakpoint_enabled(file: text, line: i64, enabled: bool)

# Execution control
extern fn rt_hook_continue()
extern fn rt_hook_pause()
extern fn rt_hook_step()
extern fn rt_hook_terminate()

# Stack inspection
extern fn rt_hook_get_call_depth() -> i64
extern fn rt_hook_get_stack_frames() -> [StackFrame]

# Variable inspection
extern fn rt_hook_get_variables(frame_id: i64, scope: VariableScope) -> [Variable]

# Expression evaluation
extern fn rt_hook_evaluate_expression(expr: text, frame_id: i64) -> EvalResult
extern fn rt_hook_evaluate_condition(condition: text) -> bool

# Debugging state
extern fn rt_hook_enable_debugging()
extern fn rt_hook_disable_debugging()
```

### Implementation Location

These FFI functions should be implemented in:
- **Rust side**: `rust/compiler/src/interpreter_hooks.rs` (new file)
- **SFFI spec**: `src/app/ffi_gen/specs/interpreter_hooks.spl` (new file)

## Implementation Strategy

### Phase 1: Breakpoint Storage (Current)

- Store breakpoints in `InterpreterHookContext`
- Notify interpreter via FFI
- Check breakpoints during execution

### Phase 2: Execution Control

Modify interpreter to check breakpoints at key points:

```rust
// In rust/compiler/src/interpreter/node_exec.rs

fn exec_statement(node: &Node) -> Result<RuntimeValue> {
    // Check if we should break at this line
    if should_break_at_line(node.location.line) {
        // Capture stack frames
        let frames = capture_stack_frames();

        // Notify debugger (pause execution)
        notify_breakpoint_hit(node.location);

        // Wait for debugger command (continue, step, etc.)
        wait_for_debugger_command();
    }

    // Normal execution
    // ...
}
```

### Phase 3: Stack Frame Capture

Capture stack frames when paused:

```rust
// In rust/compiler/src/interpreter/interpreter_state.rs

pub fn capture_stack_frames() -> Vec<StackFrame> {
    let mut frames = vec![];

    // Walk call stack
    for (i, call_info) in CALL_STACK.with(|cs| cs.borrow().clone()).iter().enumerate() {
        frames.push(StackFrame {
            id: i as i64,
            name: call_info.function_name.clone(),
            file: call_info.source_file.clone(),
            line: call_info.line,
            column: call_info.column,
            scope_id: call_info.scope_id,
        });
    }

    frames
}
```

### Phase 4: Variable Inspection

Provide variable access at each frame:

```rust
// In rust/compiler/src/interpreter/interpreter_state.rs

pub fn get_variables_in_scope(frame_id: i64, scope: VariableScope) -> Vec<Variable> {
    let frame_info = get_frame_info(frame_id);

    match scope {
        VariableScope::Local => get_local_variables(&frame_info),
        VariableScope::Argument => get_argument_variables(&frame_info),
        VariableScope::Closure => get_closure_variables(&frame_info),
        VariableScope::Global => get_global_variables(),
    }
}
```

### Phase 5: Expression Evaluation

Evaluate expressions in the context of a frame:

```rust
// In rust/compiler/src/interpreter/interpreter_eval.rs

pub fn evaluate_expression(expr: &str, frame_id: i64) -> EvalResult {
    // Parse expression
    let ast = parse_expression(expr)?;

    // Get frame context (local variables, etc.)
    let context = get_frame_context(frame_id);

    // Evaluate in context
    let value = evaluate_with_context(&ast, &context)?;

    // Convert to string representation
    EvalResult {
        value: value.to_string(),
        type_info: value.type_name(),
        error: None,
    }
}
```

## Debugging Workflow Example

Complete debugging session:

```simple
import runtime.hooks

# 1. Create and configure hook context
val hook_ctx = InterpreterHookContext.create()
hook_ctx.enable()

# 2. Set event callback
hook_ctx.set_event_callback(\event:
    match event:
        DebugEvent.Breakpoint(id):
            # Program paused at breakpoint
            val frames = hook_ctx.stack_frames()
            print "Paused at: {frames[0].file}:{frames[0].line}"

            # Show variables
            val vars = hook_ctx.variables_in_frame(0)
            for v in vars:
                print "  {v.name} = {v.value}"

        DebugEvent.Output(message):
            print "Log: {message}"

        DebugEvent.Exit(exit_code):
            print "Program exited: {exit_code}"
)

# 3. Set breakpoints
val bp1 = hook_ctx.add_breakpoint("src/main.spl", 10)
val bp2 = hook_ctx.add_breakpoint_with_options(
    file: "src/utils.spl",
    line: 25,
    condition: Some("count > 100"),
    hit_condition: None,
    log_message: None,
)

# 4. Start execution (will pause at breakpoints)
run_program()

# 5. When paused, step through code
hook_ctx.step_over()  # Execute current line
hook_ctx.step_into()  # Step into function
hook_ctx.step_out()   # Return from function

# 6. Evaluate expressions
val result = hook_ctx.evaluate("x + y", frame_id: 0)
print "x + y = {result.value}"

# 7. Continue execution
hook_ctx.continue()
```

## Performance Considerations

### Overhead When Not Debugging

- ❌ Disabled: Zero overhead (no checks)
- ✅ Enabled: Minimal overhead (line check only)

### Breakpoint Checking

Breakpoint checks should be:
- **Fast**: Hash table lookup by (file, line)
- **Infrequent**: Only at statement boundaries
- **Lazy**: Condition evaluation only when breakpoint hit

### Stack Frame Capture

- Capture only when paused (not continuously)
- Use thread-local storage for call stack
- Lazy variable evaluation

## Testing

### Unit Tests

```simple
describe "InterpreterHookContext":
    it "adds and removes breakpoints":
        val hook_ctx = InterpreterHookContext.create()
        val bp_id = hook_ctx.add_breakpoint("test.spl", 42)

        assert hook_ctx.get_breakpoints().length == 1

        hook_ctx.remove_breakpoint(bp_id)
        assert hook_ctx.get_breakpoints().length == 0

    it "evaluates hit conditions correctly":
        assert evaluate_hit_condition(5, ">= 5") == true
        assert evaluate_hit_condition(4, ">= 5") == false
        assert evaluate_hit_condition(6, "% 2 == 0") == true
        assert evaluate_hit_condition(7, "% 2 == 0") == false
```

### Integration Tests

```simple
describe "Debugging Integration":
    it "pauses at breakpoint":
        val hook_ctx = InterpreterHookContext.create()
        hook_ctx.enable()

        var paused = false
        hook_ctx.set_event_callback(\event:
            if event.is_breakpoint():
                paused = true
        )

        hook_ctx.add_breakpoint("test.spl", 5)

        run_test_program()

        assert paused
```

## Future Enhancements

### Advanced Breakpoints

- **Data breakpoints**: Break when memory changes
- **Function breakpoints**: Break on function entry
- **Exception breakpoints**: Break on specific exceptions

### Reverse Debugging

- Record execution history
- Step backwards through execution
- Reverse continue

### Time-Travel Debugging

- Snapshot program state at each step
- Jump to arbitrary points in execution history

### Hot Code Reload

- Modify code while debugging
- Apply changes without restarting

## Related Documentation

- **DAP Server**: `src/app/dap/README.md`
- **Compiler Query API**: `doc/guide/compiler_query_api_guide.md`
- **MCP Integration**: `doc/research/mcp_lsp_dap_integration_analysis.md`

## References

- DAP Specification: https://microsoft.github.io/debug-adapter-protocol/
- Simple Interpreter: `rust/compiler/src/interpreter/`
- Runtime Architecture: `rust/runtime/`
