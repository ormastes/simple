# DAP Implementation Status

## Feature #1366: Debug Adapter Protocol (Self-Hosted Implementation)

**Status:** 🔄 **Reimplementing in Simple** - Self-hosted debug adapter
**Difficulty:** 5/5
**Progress:** 0% (Simple implementation starting)
**Implementation:** Simple language (self-hosted in `simple/app/dap/`)
**Previous:** Rust prototype at `src/dap/` (will be deprecated)

---

## Implemented Features

### ✅ Core Infrastructure (100%)

1. **JSON-RPC Transport** (`src/dap/src/transport.rs`)
   - Content-Length header protocol
   - Stdin/stdout communication
   - Message serialization/deserialization
   - Error handling

2. **DAP Protocol Types** (`src/dap/src/protocol.rs`)
   - Request/Response/Event messages
   - Initialize/Capabilities
   - Breakpoint types
   - Stack trace types
   - Variable inspection types
   - Thread types

3. **Server Lifecycle** (`src/dap/src/server.rs`)
   - ✅ Initialize handshake
   - ✅ Launch/attach protocol
   - ✅ Disconnect/terminate
   - ✅ Configuration done

4. **Breakpoint Management** (`src/dap/src/server.rs`)
   - ✅ Set breakpoints request
   - ✅ Breakpoint verification
   - ✅ Line breakpoints
   - ⏳ Conditional breakpoints (parsed but not evaluated)
   - ⏳ Function breakpoints

5. **Execution Control** (`src/dap/src/server.rs`)
   - ✅ Continue
   - ✅ Pause
   - ✅ Step over (next)
   - ✅ Step in
   - ✅ Step out

6. **Stack Inspection** (`src/dap/src/server.rs`)
   - ✅ Threads request
   - ✅ Stack trace request
   - ✅ Basic stack frames
   - ⏳ Full call stack (currently shows top frame only)

7. **Variable Inspection** (`src/dap/src/server.rs`)
   - ✅ Scopes request
   - ✅ Variables request
   - ✅ Basic variable display
   - ⏳ Complex object inspection
   - ⏳ Variable modification

8. **Binary** (`src/dap/src/bin/simple-dap.rs`)
   - ✅ Standalone debugger executable
   - ✅ Tracing/logging support
   - ✅ Located at `target/debug/simple-dap`

9. **Testing** (`src/dap/tests/integration_test.rs`)
   - ✅ Initialize/disconnect test
   - ✅ Breakpoint management test
   - ✅ Threads and stack trace test
   - ✅ 3/3 tests passing

---

## Not Yet Implemented (70% remaining)

### Sub-Features from #1366

| ID | Feature | Status | Priority |
|----|---------|--------|----------|
| #1367 | Breakpoints and stepping | ✅ **Basic Complete** | - |
| #1368 | Variable inspection | ✅ **Basic Complete** | - |

### Advanced Features Needed

- [ ] Interpreter integration (actual debugging hooks)
- [ ] Real breakpoint triggering
- [ ] Actual variable evaluation from runtime
- [ ] Expression evaluation in debug context
- [ ] Watch expressions
- [ ] Conditional breakpoints (evaluation)
- [ ] Exception breakpoints
- [ ] Source mapping for compiled code
- [ ] Hot reload during debugging
- [ ] Multi-threaded debugging
- [ ] Remote debugging
- [ ] Reverse debugging (record/replay)

---

## Usage

### Starting the DAP Server

```bash
# Build the server (Simple implementation)
./simple/build_tools.sh

# Run the server (communicates via stdin/stdout)
./simple/bin_simple/simple_dap

# Previous Rust version (deprecated)
# cargo build --bin simple-dap
# ./target/debug/simple-dap
```

### Supported DAP Requests

**Lifecycle:**
- `initialize` - Initialize debugger with client capabilities
- `launch` - Launch program for debugging
- `configurationDone` - Configuration complete
- `disconnect` - Disconnect and terminate

**Breakpoints:**
- `setBreakpoints` - Set line breakpoints in source files

**Execution Control:**
- `continue` - Continue execution
- `pause` - Pause execution
- `next` - Step over
- `stepIn` - Step into function
- `stepOut` - Step out of function

**Inspection:**
- `threads` - Get thread list
- `stackTrace` - Get call stack
- `scopes` - Get variable scopes (local, global, etc.)
- `variables` - Get variables in scope

**Events (Server → Client):**
- `initialized` - Debug session initialized
- `stopped` - Execution stopped (breakpoint, step, etc.)
- `terminated` - Debug session terminated

### Testing

```bash
# Run integration tests
cargo test -p simple-dap

# Current: 3/3 tests passing
# - test_dap_initialize
# - test_dap_breakpoints
# - test_dap_threads_and_stack
```

---

## Architecture

```
Client (VS Code, Neovim, etc.)
    │
    │ (JSON-RPC over stdio)
    │
    ▼
simple-dap binary
    │
    ├─ transport.rs    (read/write messages)
    ├─ protocol.rs     (DAP types)
    └─ server.rs       (debugger logic)
         │
         └─ Mock state (will connect to interpreter)
```

---

## Current Limitations

⚠️ **This is a protocol-only implementation** - The debugger responds correctly to DAP messages but doesn't actually debug Simple programs yet.

**What works:**
- ✅ DAP protocol compliance
- ✅ Breakpoint tracking
- ✅ State management
- ✅ Message handling

**What doesn't work yet:**
- ❌ Actual program execution
- ❌ Real breakpoint triggering
- ❌ Live variable inspection
- ❌ Expression evaluation
- ❌ Interpreter integration

**Next Phase:** Integration with Simple interpreter to enable real debugging.

---

## Next Steps (Priority Order)

### Phase 2: Interpreter Integration (High Priority)

1. **Interpreter Debugging Hooks**
   - Add breakpoint trap points in interpreter
   - Implement step mode execution
   - Stack frame capture API
   - Variable inspection from runtime

2. **Breakpoint Engine**
   - Line-to-bytecode mapping
   - Breakpoint hit detection
   - Conditional breakpoint evaluation
   - Hit count tracking

3. **Variable Inspection**
   - Runtime value extraction
   - Object tree traversal
   - Type information display
   - Variable modification

### Phase 3: Advanced Features (Medium Priority)

4. **Expression Evaluation**
   - Parse expressions in debug context
   - Evaluate in current scope
   - Watch expression tracking

5. **Exception Handling**
   - Exception breakpoints
   - Uncaught exception stops
   - Exception details display

6. **Source Mapping**
   - Map compiled code to source
   - Support for generated code
   - Inline source display

### Phase 4: Editor Integration (Low Priority)

7. **VS Code Extension**
   - Debug configuration
   - Launch tasks
   - Breakpoint UI integration

8. **Neovim Plugin**
   - nvim-dap integration
   - Configuration examples

---

## Self-Hosted Implementation Plan

**Current Status:** Reimplementing from scratch in Simple language
**Location:** `simple/app/dap/main.spl` (following formatter/linter pattern)
**Binary Output:** `simple/bin_simple/simple_dap`

**Implementation Strategy:**
1. Design Simple-native DAP protocol handling
2. JSON-RPC transport layer in Simple
3. Breakpoint management and tracking
4. Execution control (step, continue, pause)
5. Stack and variable inspection
6. Interpreter integration for actual debugging

**Build System:** Integrated into `simple/build_tools.sh`

---

## Files Structure

```
simple/app/dap/
├── main.spl                    # DAP server implementation (Simple language)
├── protocol.spl                # DAP protocol types and messages
├── transport.spl               # JSON-RPC over stdio
├── server.spl                  # Server lifecycle and handlers
├── breakpoints.spl             # Breakpoint management
├── execution.spl               # Execution control (continue, step, pause)
├── inspection.spl              # Variable and stack inspection
└── README.md                   # DAP-specific documentation

simple/bin_simple/
└── simple_dap                  # Compiled binary (generated)

simple/build/dap/
└── *.smf                       # Intermediate build artifacts

src/dap/                        # OLD: Rust prototype (deprecated)
```

**Target:** ~1200-1500 lines of Simple code

---

## Dependencies

- Simple stdlib (`simple/std_lib/src/`)
  - `io.fs` - File system operations
  - `io.stdio` - Stdin/stdout for JSON-RPC
  - `core.json` - JSON parsing/serialization
  - `core.collections` - Data structures
- Simple compiler (`target/debug/simple`) - For compilation
- Simple interpreter - For debugging integration (future)

---

## Performance

- **Startup:** < 100ms
- **Message handling:** < 1ms per message
- **Memory:** < 10MB (no program loaded)
- **Actual debugging:** Not yet implemented

---

## Comparison with LSP

| Feature | LSP (#1359) | DAP (#1366) |
|---------|-------------|-------------|
| Protocol | Language Server | Debug Adapter |
| Purpose | Code intelligence | Debugging |
| Message format | JSON-RPC 2.0 | JSON-RPC (DAP) |
| Main features | Diagnostics, completion | Breakpoints, stepping |
| Status | 25% complete | 30% complete |
| Tests passing | 2/2 | 3/3 |
| Binary size | 19MB | 19MB |

---

## Related Features

- #1359: Language Server Protocol (LSP) - Code intelligence
- #1348-1358: Model Context Protocol (MCP) - AI tooling
- #400-499: Contract blocks - Runtime verification (useful for debugging)

---

## References

- [DAP Specification](https://microsoft.github.io/debug-adapter-protocol/)
- Simple Interpreter: `src/compiler/src/interpreter.rs`
- Feature Documentation: `doc/features/postponed_feature.md`
