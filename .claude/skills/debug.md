# Debug Skill - Simple Compiler Debugging

## Logging Setup

### Enable Tracing
```bash
# Set log level
SIMPLE_LOG=debug ./rust/target/debug/simple file.spl
RUST_LOG=debug ./rust/target/debug/simple file.spl

# Specific module
SIMPLE_LOG=simple_compiler::interpreter=trace ./rust/target/debug/simple file.spl

# Multiple modules
SIMPLE_LOG=simple_compiler=debug,simple_runtime=trace ./rust/target/debug/simple file.spl
```

### GC Logging
```bash
# Enable GC debug output
./rust/target/debug/simple --gc-log file.spl

# See allocation/collection events
SIMPLE_LOG=simple_runtime::memory::gc=debug ./rust/target/debug/simple file.spl
```

## Interpreter Debugging

### Interpreter Modules
```
src/compiler/src/
├── interpreter.rs          # Main entry point
├── interpreter_call.rs     # Function calls
├── interpreter_control.rs  # Control flow (if, match, loops)
├── interpreter_context.rs  # Execution context
├── interpreter_extern.rs   # External function bindings
├── interpreter_ffi.rs      # FFI bridge
├── interpreter_helpers.rs  # Utilities
├── interpreter_macro.rs    # Macro expansion
└── interpreter_method.rs   # Method dispatch
```

### Add Debug Tracing
```rust
use tracing::{debug, trace, instrument};

#[instrument(skip(self))]
fn interpret_expr(&mut self, expr: &Expr) -> Result<Value> {
    trace!(?expr, "interpreting expression");
    // ...
    debug!(result = ?value, "expression result");
    Ok(value)
}
```

### Value Inspection
```rust
// In interpreter code
use crate::value::Value;

// Debug print runtime values
eprintln!("Value: {:?}", value);
eprintln!("Type: {:?}", value.type_of());

// For RuntimeValue (tagged pointer)
use simple_runtime::value::RuntimeValue;
eprintln!("Tag: {:?}", rv.tag());
eprintln!("Is heap: {}", rv.is_heap_object());
```

## Codegen Debugging

### IR Export
```bash
# Export AST
./rust/target/debug/simple --emit-ast=ast.json file.spl

# Export HIR (type-checked)
./rust/target/debug/simple --emit-hir=hir.json file.spl

# Export MIR (lowered)
./rust/target/debug/simple --emit-mir=mir.json file.spl

# All to stdout
./rust/target/debug/simple --emit-ast --emit-hir --emit-mir file.spl
```

### Compilability Analysis
Check why code falls back to interpreter:
```rust
// src/compiler/src/compilability.rs
// 20+ fallback reasons tracked

// In logs, look for:
// "Falling back to interpreter: <reason>"
```

### Cranelift Debug
```bash
# Enable Cranelift IR dumps
CRANELIFT_DEBUG=1 ./rust/target/debug/simple --compile file.spl
```

## Runtime Debugging

### RuntimeValue Structure
```
64-bit tagged pointer:
┌──────────────────────────────────────────────────────┐
│ Payload (48-62 bits)              │ Tag (2-16 bits)  │
└──────────────────────────────────────────────────────┘

Tags:
- 0b00: Pointer (heap object)
- 0b01: Small integer
- 0b10: Special (nil, true, false)
- 0b11: Symbol
```

### Heap Object Inspection
```rust
use simple_runtime::value::{HeapHeader, HeapObjectType};

// Check heap object type
if let Some(header) = rv.as_heap_header() {
    eprintln!("Object type: {:?}", header.object_type);
    eprintln!("Size: {}", header.size);
}
```

## Test Debugging

### Run Single Test with Output
```bash
cd rust && cargo test -p simple-driver test_name -- --nocapture

# With logging
RUST_LOG=debug cargo test -p simple-driver test_name -- --nocapture
```

### Debug Simple Test
```bash
# Run with verbose output
./rust/target/debug/simple --verbose src/std/test/unit/core/test_spec.spl

# Step through (if DAP available)
./rust/target/debug/simple --debug src/std/test/unit/core/test_spec.spl
```

## Fault Detection

### Stack Overflow Detection
```bash
# Enabled by default in debug builds, disabled in release
SIMPLE_STACK_OVERFLOW_DETECTION=1 ./rust/target/debug/simple_old file.spl

# Set custom recursion depth limit (default: 1000)
SIMPLE_MAX_RECURSION_DEPTH=500 ./rust/target/debug/simple_old file.spl
```
- Implemented in `interpreter_state.rs` (AtomicUsize + RAII guard)
- ~2 atomic ops per function call (Relaxed ordering)
- Error: `StackOverflow { depth, limit, function_name }`

### Timeout Detection (Wall-Clock)
```bash
# Set execution timeout in seconds (0 = disabled, default)
SIMPLE_TIMEOUT_SECONDS=30 ./rust/target/debug/simple_old file.spl

# Short timeout for testing infinite loops
SIMPLE_TIMEOUT_SECONDS=1 ./rust/target/debug/simple_old loop_test.spl
```
- Watchdog thread checks every 100ms via `watchdog.rs`
- Zero overhead on fast path (single AtomicBool load, Relaxed)
- Checked at loop back-edges alongside `check_interrupt!()` and `check_execution_limit!()`

### Crash Detection (catch_unwind)
- `run_file_with_args` and `run_code` in `cli/basic.rs` wrap execution in `catch_unwind`
- Panics produce: `fatal: interpreter crashed: <message>` (exit code 101)
- Panic hook in `cli/init.rs` logs backtrace to stderr and tracing

### Memory Leak Detection
```bash
# Enable heap growth heuristic (opt-in)
SIMPLE_LEAK_DETECTION=1 ./rust/target/debug/simple_old file.spl
```
- Tracks post-GC heap size over 10 cycles
- Warns via `tracing::warn!` if heap grows >10% over window
- Zero overhead when disabled; runs only in GC collection path

### Execution Limit (existing)
```bash
# Set instruction count limit (default: 10M, 0 = disabled)
SIMPLE_EXECUTION_LIMIT=1000000 ./rust/target/debug/simple_old file.spl
SIMPLE_EXECUTION_LIMIT_ENABLED=false ./rust/target/debug/simple_old file.spl
```

### Sanitizer Support
```bash
# Address Sanitizer (requires nightly)
RUSTFLAGS="-Zsanitizer=address" cargo +nightly test -p simple-driver

# Valgrind
valgrind --leak-check=full ./rust/target/debug/simple_old file.spl
```

### Env Var Summary
| Variable | Default | Purpose |
|---|---|---|
| `SIMPLE_STACK_OVERFLOW_DETECTION` | debug=on, release=off | Recursion depth check |
| `SIMPLE_MAX_RECURSION_DEPTH` | 1000 | Max call depth |
| `SIMPLE_TIMEOUT_SECONDS` | 0 (off) | Wall-clock timeout |
| `SIMPLE_EXECUTION_LIMIT` | 10000000 | Instruction count limit |
| `SIMPLE_EXECUTION_LIMIT_ENABLED` | debug=on, release=off | Enable instruction limit |
| `SIMPLE_LEAK_DETECTION` | false | Heap growth heuristic |

## Common Issues

### "Falling back to interpreter"
- Check `compilability.rs` for reason
- Usually: unsupported MIR instruction, complex pattern, dynamic dispatch

### Memory Issues
- Enable GC logging: `--gc-log`
- Check for leaks with `SIMPLE_LOG=simple_runtime::memory=debug`
- Enable leak detection: `SIMPLE_LEAK_DETECTION=1`

### Type Errors
- Export HIR: `--emit-hir` to see inferred types
- Check unification in `src/type/src/lib.rs`

### Pattern Match Failures
- MIR patterns in `src/compiler/src/mir/types.rs`
- PatternTest/PatternBind instructions

## Useful Debug Patterns

### Conditional Breakpoint (in tests)
```rust
#[test]
fn debug_specific_case() {
    if std::env::var("DEBUG_TEST").is_ok() {
        // Extra debug output
        eprintln!("Debug info...");
    }
}
```

### Panic Location
```bash
RUST_BACKTRACE=1 cargo test -p simple-driver test_name
RUST_BACKTRACE=full cargo test -p simple-driver test_name
```

## MCP-Based Debugging (NEW)

### Start MCP Server
```bash
# Start MCP server for interactive debugging
./rust/target/debug/simple_old src/app/mcp/main.spl server --debug

# CLI mode - read/analyze files
./rust/target/debug/simple_old src/app/mcp/main.spl read src/compiler/driver.spl
./rust/target/debug/simple_old src/app/mcp/main.spl json src/compiler/driver.spl
```

### MCP Tools Available
- `read_code <file>` - Read Simple source files with syntax highlighting
- `list_files <dir>` - List .spl files in directory
- `search_code <query>` - Search for code patterns
- `file_info <file>` - Get file statistics (lines, functions, classes)

### Bootstrap Debugging
```bash
# Run bootstrap with debug capture
./scripts/capture_bootstrap_debug.sh

# Run specific stage
./scripts/bootstrap.sh --stage=1    # simple_old → simple_new1
./scripts/bootstrap.sh --stage=2    # simple_new1 → simple_new2

# Verify determinism
./scripts/bootstrap.sh --verify

# Extended multi-generation test
./rust/target/debug/simple_old scripts/bootstrap_extended.spl --generations=5
```

### Debug Instrumentation Points

**Phase 3 (HIR Lowering):**
```
[phase3] parsed modules count=N
[phase3] DEBUG: module_names = [...]
[phase3] stored HIR module 'X', total now: N
[phase3] loop complete. HIR modules keys: [...]
[phase3] returning ctx with N HIR modules
```

**Phase 5 (AOT Compilation):**
```
[aot] DEBUG: ctx.hir_modules count = N
[aot] lowering to MIR...
[aot] MIR done, N modules
```

### Common Bootstrap Issues

**Issue: "MIR done, 0 modules"**
- HIR modules created in phase 3 but lost before phase 5
- Check context flow: `[compile] BEFORE/AFTER phase 3`
- Verify: `ctx.hir_modules.keys().len()` at each phase

**Issue: "No object files to link"**
- MIR lowering found 0 HIR modules to process
- Root cause: Context not preserved between phases
- Debug: Add prints in `lower_and_check_impl()` return

**Issue: Bootstrap timeout (>60s)**
- Large debug output slowing compilation
- Use `SIMPLE_LOG=warn` to reduce verbosity
- Profile with: `time ./scripts/bootstrap.sh --stage=1`

### Automated Bug Detection

**Test Dictionary Semantics:**
```bash
./rust/target/debug/simple_old scripts/test_dict_semantics.spl
# Should show: "ALL TESTS PASSED"
```

**MCP Debug Script:**
```bash
./rust/target/debug/simple_old scripts/mcp_debug_bootstrap.spl
# Auto-detects common bug patterns
```

### Bug Database

**View registered bugs:**
```bash
cat doc/bug/bug_db.sdn
# SDN format: bugs, test_cases, fixes, notes
```

**Bug Analysis Reports:**
- `doc/bug/mcp_bug_analysis_2026-01-29.md` - MCP analysis
- `doc/bug/bootstrap_mir_zero_modules.md` - Bootstrap bug details
- `doc/report/bootstrap_investigation_2026-01-29.md` - Investigation log

### Live Debugging Workflow

1. **Capture Debug Output:**
   ```bash
   ./scripts/capture_bootstrap_debug.sh
   # Saves to: target/bootstrap_debug_TIMESTAMP.log
   ```

2. **Extract Key Messages:**
   ```bash
   grep -E "\[phase3\]|\[aot\]" target/bootstrap_debug_*.log
   ```

3. **Identify Loss Point:**
   - Compare HIR module count at phase 3 exit vs phase 5 entry
   - If phase 3 shows N but phase 5 shows 0, modules lost between

4. **Register Bug:**
   ```bash
   # Add to doc/bug/bug_db.sdn
   bugs |id, severity, status, title, file, line, description|
       bug_id, P0, confirmed, "Description", "file.spl", 123, "Details", "test_case"
   ```

5. **Apply Fix & Test:**
   ```bash
   # After fixing
   cargo build
   ./scripts/bootstrap.sh --verify
   ```

## See Also

- `src/runtime/src/memory/gc.rs` - GC implementation
- `src/compiler/src/value.rs` - Value enum, Env
- `src/runtime/src/value/` - RuntimeValue (9 modules)
- `doc/codegen_technical.md` - Codegen details
- `doc/bug/bug_db.sdn` - Bug tracking database
- `scripts/mcp_debug_bootstrap.spl` - MCP debugger
- `scripts/bootstrap_extended.spl` - Multi-gen bootstrap tester
