# Debug Skill - Simple Compiler Debugging

## Logging Setup

### Enable Tracing
```bash
# Set log level
SIMPLE_LOG=debug ./target/debug/simple file.spl
RUST_LOG=debug ./target/debug/simple file.spl

# Specific module
SIMPLE_LOG=simple_compiler::interpreter=trace ./target/debug/simple file.spl

# Multiple modules
SIMPLE_LOG=simple_compiler=debug,simple_runtime=trace ./target/debug/simple file.spl
```

### GC Logging
```bash
# Enable GC debug output
./target/debug/simple --gc-log file.spl

# See allocation/collection events
SIMPLE_LOG=simple_runtime::memory::gc=debug ./target/debug/simple file.spl
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
./target/debug/simple --emit-ast=ast.json file.spl

# Export HIR (type-checked)
./target/debug/simple --emit-hir=hir.json file.spl

# Export MIR (lowered)
./target/debug/simple --emit-mir=mir.json file.spl

# All to stdout
./target/debug/simple --emit-ast --emit-hir --emit-mir file.spl
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
CRANELIFT_DEBUG=1 ./target/debug/simple --compile file.spl
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
cargo test -p simple-driver test_name -- --nocapture

# With logging
RUST_LOG=debug cargo test -p simple-driver test_name -- --nocapture
```

### Debug Simple Test
```bash
# Run with verbose output
./target/debug/simple --verbose simple/std_lib/test/unit/core/test_spec.spl

# Step through (if DAP available)
./target/debug/simple --debug simple/std_lib/test/unit/core/test_spec.spl
```

## Common Issues

### "Falling back to interpreter"
- Check `compilability.rs` for reason
- Usually: unsupported MIR instruction, complex pattern, dynamic dispatch

### Memory Issues
- Enable GC logging: `--gc-log`
- Check for leaks with `SIMPLE_LOG=simple_runtime::memory=debug`

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

## See Also

- `src/runtime/src/memory/gc.rs` - GC implementation
- `src/compiler/src/value.rs` - Value enum, Env
- `src/runtime/src/value/` - RuntimeValue (9 modules)
- `doc/codegen_technical.md` - Codegen details
