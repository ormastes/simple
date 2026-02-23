# Simple MCP Debug Server - Design Document

## Overview

Unified MCP server with integrated debugger supporting 3 targets: interpreter, SMF bytecode, and native binaries. The server exposes debug, session, edit, and code view tools via MCP JSON-RPC.

## Architecture

```
+-------------------------------------+
|     Unified MCP Server              |
|  (src/app/mcp/main.spl - enhanced) |
|                                     |
|  Tools: session, view, lsp,        |
|         debug, edit                 |
+----------------+--------------------+
                 |
      +----------+----------+
      |  Debug Coordinator  |
      |  + Session Manager  |
      +----------+----------+
                 |
      +----------+----------+---------+
      |          |                    |
  +---v---+  +--v----+  +-----------v+
  |Interp |  | SMF   |  | Native    |
  |Backend|  |Backend|  | Backend   |
  +-------+  +-------+  +-----------+
```

## Components

### Rust Layer (FFI primitives only)

- **`src/rust/runtime/src/debug.rs`** - DebugState singleton with:
  - Breakpoint management (add/remove/check)
  - Step mode tracking (Continue/StepOver/StepIn/StepOut)
  - Call stack with frame locals
  - `should_stop(file, line)` combining breakpoints + step logic
  - 14 `rt_debug_*` FFI functions for Simple-side access

- **`src/rust/compiler/src/interpreter/node_exec.rs`** - Debug hook in `exec_node()`:
  - Checks `debug_state().should_stop()` before each statement
  - Captures local variables snapshot when paused
  - Zero overhead when debugger inactive (`ds.active` check)

- **`src/rust/compiler/src/codegen/runtime_ffi.rs`** - FFI specs for codegen

### Simple Layer (all orchestration logic)

#### Session Management (`src/app/mcp/session.spl`)
- `SessionManager` - manages multiple debug sessions
- `DebugSession` - tracks target type, state, breakpoints per session
- `SessionBreakpoint` - breakpoint with condition/hit count

#### Debug Coordinator (`src/app/debug/coordinator.spl`)
- `DebugBackend` trait - interface all backends implement:
  - `attach`, `detach`, `run`, `pause`, `resume`
  - `step_over`, `step_in`, `step_out`
  - `add_breakpoint`, `remove_breakpoint`
  - `stack_trace`, `locals`, `evaluate`, `current_location`
- `DebugCoordinator` - routes commands to correct backend based on session target
- `FrameInfo`, `VarInfo`, `LocationInfo` - data types for inspection results

#### Interpreter Backend (`src/app/debug/interpreter_backend.spl`)
- Implements `DebugBackend` for tree-walking interpreter
- Delegates to `rt_debug_*` FFI functions
- Activates/deactivates debug state on attach/detach

#### SMF Backend (`src/app/debug/smf_agent.spl`)
- Implements `DebugBackend` for SMF bytecode
- Uses `rt_ptrace_*` FFI for process control
- INT3 breakpoint insertion with byte save/restore
- Source map lookup for bytecode-to-source mapping

#### Native Backend (`src/app/debug/native_agent.spl`)
- Implements `DebugBackend` for ELF/Mach-O binaries
- Uses ptrace FFI (shared with SMF) + DWARF FFI
- `rt_dwarf_*` functions for addr-to-line, function lookup, locals

#### Document Editor (`src/app/mcp/editor.spl`)
- `DocumentManager` - tracks open documents with line-based editing
- `ManagedDocument` - cached content with version tracking
- Operations: insert, delete, replace, copy, save

### MCP Tools Registered

| Tool | Description | Phase |
|------|-------------|-------|
| `debug_run` | Start/resume/pause/terminate sessions | 1 |
| `debug_break` | Add/remove/list/clear breakpoints | 1 |
| `debug_step` | Step over/in/out | 1 |
| `debug_inspect` | Stack trace, locals, evaluate, location | 1 |
| `debug_session` | List/info/terminate sessions | 1 |
| `edit_insert` | Insert text at line | 4 |
| `edit_delete` | Delete line range | 4 |
| `edit_replace` | Replace line range | 4 |
| `edit_copy` | Copy line range | 4 |
| `code_view` | View code range | 4 |

## FFI Functions

### Debug FFI (`rt_debug_*`)

| Function | Signature | Purpose |
|----------|-----------|---------|
| `rt_debug_set_active` | `(i64) -> ()` | Enable/disable debugger |
| `rt_debug_is_active` | `() -> i64` | Check if active |
| `rt_debug_add_breakpoint` | `(i64, i64, i64) -> i64` | Add breakpoint, returns id |
| `rt_debug_remove_breakpoint` | `(i64, i64, i64) -> i64` | Remove breakpoint |
| `rt_debug_remove_all_breakpoints` | `() -> ()` | Clear all breakpoints |
| `rt_debug_list_breakpoints` | `() -> RuntimeValue` | Array of "file:line" strings |
| `rt_debug_set_step_mode` | `(i64) -> ()` | 0=run,1=over,2=in,3=out |
| `rt_debug_pause` | `() -> ()` | Request pause |
| `rt_debug_continue` | `() -> ()` | Resume execution |
| `rt_debug_stack_depth` | `() -> i64` | Call stack depth |
| `rt_debug_stack_trace` | `() -> RuntimeValue` | Array of frame strings |
| `rt_debug_locals` | `() -> RuntimeValue` | Array of "name = val : type" |
| `rt_debug_current_file` | `() -> RuntimeValue` | Current file path |
| `rt_debug_current_line` | `() -> i64` | Current line number |

### Ptrace FFI (`rt_ptrace_*`) - Phase 2/3

| Function | Purpose |
|----------|---------|
| `rt_ptrace_attach` | Attach to process |
| `rt_ptrace_detach` | Detach from process |
| `rt_ptrace_continue` | Resume process |
| `rt_ptrace_single_step` | Execute one instruction |
| `rt_ptrace_read_memory` | Read process memory |
| `rt_ptrace_write_memory` | Write process memory |
| `rt_ptrace_get_registers` | Get CPU registers |
| `rt_ptrace_wait_stop` | Wait for process stop |

### DWARF FFI (`rt_dwarf_*`) - Phase 3

| Function | Purpose |
|----------|---------|
| `rt_dwarf_load` | Load DWARF info from binary |
| `rt_dwarf_free` | Free DWARF handle |
| `rt_dwarf_addr_to_line` | Map address to source location |
| `rt_dwarf_function_at` | Get function name at address |
| `rt_dwarf_locals_at` | Get local variables at address |
| `rt_dwarf_line_to_addr` | Map source line to address |

## Implementation Phases

### Phase 0: Interpreter Debug Hooks (DONE)
- `src/rust/runtime/src/debug.rs` - DebugState + FFI
- `src/rust/compiler/src/interpreter/node_exec.rs` - Hook in exec_node
- `src/rust/compiler/src/codegen/runtime_ffi.rs` - FFI specs

### Phase 1: MCP Debug + Session Tools (DONE)
- `src/app/mcp/session.spl` - SessionManager
- `src/app/debug/coordinator.spl` - DebugCoordinator + DebugBackend trait
- `src/app/debug/interpreter_backend.spl` - Interpreter debug backend
- `src/app/mcp/main.spl` - 5 debug tools + 5 edit tools registered

### Phase 2: SMF Debug Backend (DONE - stub)
- `src/app/debug/smf_agent.spl` - SmfBackend implementing DebugBackend
- Needs: `rt_ptrace_*` Rust FFI implementation

### Phase 3: Native Binary Debug Backend (DONE - stub)
- `src/app/debug/native_agent.spl` - NativeBackend with DWARF
- Needs: `rt_dwarf_*` Rust FFI (gimli crate) + `rt_ptrace_*`

### Phase 4: LSP Enhancement + Edit Tools (DONE)
- `src/app/mcp/editor.spl` - DocumentManager with transactional edits
- Edit tools registered in MCP server

### Phase 5: Advanced Features (TODO)
- Conditional breakpoints (condition field exists, eval not wired)
- Watchpoints
- Async/actor debugging
- Hot code reload
- Multi-session support (framework ready, needs concurrent execution)

## Key Design Decisions

1. **DebugBackend trait** - All 3 backends implement same interface
2. **FFI-first debug hooks** - Rust provides primitives, Simple orchestrates
3. **Ptrace for SMF/native** - INT3 breakpoint insertion, platform-abstracted
4. **Session management** - Each session tracks target type, state, breakpoints
5. **Zero-overhead when inactive** - `ds.active` check is first in debug hook
6. **Local variable capture** - Snapshots env on pause (limited to 50 vars)

## Verification Plan

1. **Phase 0:** Set breakpoint, run interpreter, verify `should_stop` returns true
2. **Phase 1:** Start MCP server, call debug tools via JSON-RPC
3. **Phase 2:** Compile to SMF, attach, verify INT3 breakpoint hit
4. **Phase 3:** Debug native binary, verify DWARF stack traces
5. **Phase 4:** Call `edit_replace`, verify file modified correctly

## Files Created/Modified

### New Files
- `src/rust/runtime/src/debug.rs`
- `src/app/mcp/session.spl`
- `src/app/mcp/editor.spl`
- `src/app/debug/coordinator.spl`
- `src/app/debug/interpreter_backend.spl`
- `src/app/debug/smf_agent.spl`
- `src/app/debug/native_agent.spl`

### Modified Files
- `src/rust/runtime/src/lib.rs` - Added `pub mod debug` + re-exports
- `src/rust/compiler/src/codegen/runtime_ffi.rs` - Added 14 debug FFI specs
- `src/rust/compiler/src/interpreter/node_exec.rs` - Debug hook in exec_node
- `src/app/mcp/main.spl` - Registered 10 new tools (5 debug + 5 edit)
