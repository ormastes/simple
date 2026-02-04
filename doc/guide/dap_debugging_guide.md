# DAP Debugging Guide

The Simple language includes full Debug Adapter Protocol (DAP) support, enabling rich debugging experiences in VS Code and other IDEs.

## Features

✅ **Breakpoints** - Set breakpoints on any line, pause execution
✅ **Step Execution** - Step over, step into, step out of functions
✅ **Stack Traces** - View call stack with file/line information
✅ **Variable Inspection** - Inspect local and global variables
✅ **Pause/Continue** - Pause and resume execution at any time
✅ **Multiple Threads** - Debug multi-threaded Simple programs (planned)

## Quick Start

### 1. Install VS Code Extension

```bash
# The Simple VS Code extension is in src/app/vscode_extension/
cd src/app/vscode_extension
npm install
npm run compile
code --install-extension .
```

### 2. Open a Simple Project

```bash
cd your-simple-project
code .
```

### 3. Set Breakpoints

Click in the gutter (left margin) of any `.spl` file to set breakpoints. They'll appear as red dots.

### 4. Start Debugging

Press **F5** or click "Run > Start Debugging"

Choose a launch configuration:
- **Debug Simple Program** - Debug the currently open file
- **Debug Simple Tests** - Debug all tests
- **Debug Current File** - Debug from current file's directory

### 5. Use Debug Controls

| Action | Shortcut | Description |
|--------|----------|-------------|
| Continue | F5 | Resume execution until next breakpoint |
| Step Over | F10 | Execute current line, don't enter functions |
| Step Into | F11 | Execute current line, enter functions |
| Step Out | Shift+F11 | Execute until current function returns |
| Pause | F6 | Pause execution at current line |
| Stop | Shift+F5 | Stop debugging session |

## Architecture

### Components

```
┌─────────────────┐
│   VS Code IDE   │
│  (DAP Client)   │
└────────┬────────┘
         │ JSON-RPC over stdio
         │
┌────────▼────────────────┐
│  Simple DAP Server      │
│  src/app/dap/server.spl │
└────────┬────────────────┘
         │ FFI calls
         │
┌────────▼──────────────────┐
│   Rust Debug State        │
│   bootstrap_ffi_debug.rs  │
│   - Breakpoints           │
│   - Step modes            │
│   - Stack frames          │
│   - Variables             │
└────────┬──────────────────┘
         │ Debug hooks
         │
┌────────▼──────────────────┐
│  Simple Interpreter       │
│  src/compiler/backend.spl │
│  - Expression evaluation  │
│  - Breakpoint checks      │
│  - Location tracking      │
└───────────────────────────┘
```

### Debug Flow

1. **VS Code** sends DAP initialize request
2. **DAP Server** sets up debug state, responds with capabilities
3. **VS Code** sends setBreakpoints with file/line numbers
4. **DAP Server** calls `debug_add_breakpoint()` FFI
5. **Rust FFI** stores breakpoint in `DEBUG_STATE`
6. **VS Code** sends launch/attach request
7. **DAP Server** starts interpreter with debug mode active
8. **Interpreter** calls `debug_set_current_location()` on each expression
9. **Interpreter** calls `debug_should_break()` - checks breakpoints + step mode
10. If break condition met:
    - **Interpreter** calls `debug_wait_for_continue()`
    - **DAP Server** sends "stopped" event to VS Code
    - **VS Code** displays current location, variables, stack
11. User clicks Continue/Step
12. **DAP Server** calls `debug_continue()` or sets step mode
13. Loop continues until program ends

## Breakpoint Management

### Setting Breakpoints

```typescript
// VS Code sends this request
{
  "type": "request",
  "command": "setBreakpoints",
  "arguments": {
    "source": { "path": "/path/to/file.spl" },
    "breakpoints": [
      { "line": 10 },
      { "line": 25, "condition": "x > 5" }  // Conditional (planned)
    ]
  }
}
```

### Breakpoint Storage

Breakpoints are stored in Rust global state:

```rust
static DEBUG_STATE: Mutex<DebugState> = Mutex::new(DebugState {
    breakpoints: HashMap<(String, i64), BreakpointInfo>,
    // key: (file_path, line_number)
    // ...
});
```

### Breakpoint Checking

On every expression evaluation, the interpreter checks:

```simple
if debug_is_active():
    debug_set_current_location(span.file, span.line, span.column)
    if debug_should_break():
        debug_wait_for_continue()  # Blocks until user clicks Continue
```

## Step Modes

### Step Over (F10)

Execute the current line without entering function calls.

**Implementation:**
- Records current stack depth
- Sets mode to `StepOver` (1)
- Breaks when depth <= start_depth

```simple
debug_set_step_mode(1)
debug_set_step_start_depth(current_depth)
debug_continue()
```

### Step Into (F11)

Execute the current line and enter any function calls.

**Implementation:**
- Sets mode to `StepIn` (2)
- Breaks at next line regardless of depth

```simple
debug_set_step_mode(2)
debug_continue()
```

### Step Out (Shift+F11)

Execute until the current function returns.

**Implementation:**
- Records current stack depth
- Sets mode to `StepOut` (3)
- Breaks when depth < start_depth

```simple
debug_set_step_mode(3)
debug_set_step_start_depth(current_depth)
debug_continue()
```

## Variable Inspection

### Local Variables

When stopped at a breakpoint, VS Code requests local variables:

```typescript
{
  "type": "request",
  "command": "variables",
  "arguments": {
    "variablesReference": 1  // 1 = locals, 2 = globals
  }
}
```

**Implementation:**

1. DAP Server calls `debug_locals()` FFI
2. Returns format: `"name1:value1\nname2:value2\n..."`
3. Parser extracts name/value pairs
4. Sends Variable objects to VS Code

### Global Variables

Similar to locals but with `variablesReference: 2`.

### Complex Values

For objects, arrays, structs:
- Display summary: `"<TypeName { ... 5 fields }>"`
- Expandable in VS Code (planned)
- Nested variable inspection (planned)

## Stack Traces

When stopped, VS Code requests the call stack:

```typescript
{
  "type": "request",
  "command": "stackTrace",
  "arguments": {
    "threadId": 1
  }
}
```

**Implementation:**

1. DAP Server calls `debug_stack_trace()` FFI
2. Returns format: `"file:line:column:function_name\n..."`
3. Parses into StackFrame objects
4. Each frame shows:
   - Function name
   - File path (clickable)
   - Line and column numbers

### Stack Frame Display

```
main (file.spl:45)
  ├─ process_data (utils.spl:12)
  │   ├─ validate (validation.spl:78)
  │   └─ [current] transform (transform.spl:34)  ← execution stopped here
  └─ save_result (db.spl:156)
```

## Debugging Strategies

### Finding Bugs

1. **Set breakpoint** near suspected issue
2. **Run debugger** (F5)
3. **Inspect variables** in Variables pane
4. **Step through** code line-by-line
5. **Check stack** to understand call chain

### Common Scenarios

**Null Pointer / Nil Value:**
```simple
# Set breakpoint here
val user = get_user(id)  # ← Check if user is nil
val name = user.name     # ← May crash if user is nil
```

**Infinite Loop:**
```simple
# Set breakpoint inside loop
while condition:  # ← Pause here, inspect condition
    # Check why condition never becomes false
    do_work()
```

**Wrong Calculation:**
```simple
val result = calculate(a, b)  # ← Step into to see intermediate values
print result
```

## Performance Impact

The debug infrastructure has minimal overhead:

- **Debug mode OFF**: Zero overhead (all checks return immediately)
- **Debug mode ON**: ~5-10% slowdown from location tracking
- **At breakpoint**: No overhead (execution paused)
- **Step mode**: Minimal overhead (single check per line)

## Troubleshooting

### Breakpoints Not Hit

**Symptom:** Execution doesn't stop at breakpoints

**Causes:**
1. Debug mode not active
   - Solution: Ensure `debug_set_active(true)` called
2. Source path mismatch
   - Solution: Check file paths match exactly
3. Code not executed
   - Solution: Verify code path is reached

### Variables Show "undefined"

**Symptom:** Variables pane shows "(no local variables)"

**Causes:**
1. Not stopped at a location
2. No variables in current scope
3. Variable capture not implemented for this value type

### Stack Trace Empty

**Symptom:** Call Stack pane shows only "main"

**Causes:**
1. Stack frame tracking not enabled
2. Not inside a function call
3. Stack frames not properly pushed/popped

## Advanced Topics

### Conditional Breakpoints (Planned)

```json
{
  "line": 42,
  "condition": "user.age > 18"
}
```

### Hit Count Breakpoints (Planned)

Break only after N hits:

```json
{
  "line": 42,
  "hitCondition": "> 100"
}
```

### Logpoints (Planned)

Print to console without stopping:

```json
{
  "line": 42,
  "logMessage": "Value of x: {x}"
}
```

### Remote Debugging (Planned)

Debug Simple programs running on remote machines:

```bash
simple debug --remote=192.168.1.100:4711 program.spl
```

## API Reference

### FFI Functions

All debug FFI functions are in `src/ffi/debug.spl`:

**State Management:**
- `debug_is_active() -> bool`
- `debug_set_active(active: bool)`

**Breakpoints:**
- `debug_add_breakpoint(file: text, line: i64, id: i64)`
- `debug_remove_breakpoint(file: text, line: i64)`
- `debug_has_breakpoint(file: text, line: i64) -> bool`

**Execution Control:**
- `debug_pause()`
- `debug_continue()`
- `debug_is_paused() -> bool`
- `debug_wait_for_continue()`

**Stepping:**
- `debug_set_step_mode(mode: i64)` - 0=Continue, 1=StepOver, 2=StepIn, 3=StepOut
- `debug_set_step_start_depth(depth: i64)`
- `debug_should_break() -> bool`

**Location Tracking:**
- `debug_set_current_location(file: text, line: i64, column: i64)`
- `debug_current_file() -> text`
- `debug_current_line() -> i64`

**Stack Frames:**
- `debug_push_frame(func: text, file: text, line: i64, column: i64)`
- `debug_pop_frame()`
- `debug_stack_depth() -> i64`
- `debug_stack_trace() -> text` - Returns JSON

**Variables:**
- `debug_locals() -> text` - Returns "name:value\n..." format
- `debug_set_local(name: text, value: text)`
- `debug_set_global(name: text, value: text)`

## See Also

- [DAP Specification](https://microsoft.github.io/debug-adapter-protocol/)
- [VS Code Debugging](https://code.visualstudio.com/docs/editor/debugging)
- [Simple Language Guide](./language_guide.md)
- [Simple Testing Guide](./testing_guide.md)
