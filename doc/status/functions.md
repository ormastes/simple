# Feature #7: Functions

**Status**: Interpreter Complete | Native Codegen: Stub
**Difficulty**: 3/5
**Importance**: 5/5

## Summary

Functions with parameters, return types, and closures are fully supported in the tree-walking interpreter.

## Syntax

```simple
fn add(a: i32, b: i32) -> i32:
    return a + b

fn greet(name: str):
    print("Hello, {name}")

# With default parameters
fn power(base: i32, exp: i32 = 2) -> i32:
    return base ** exp

# Async function
async fn fetch_data() -> str:
    return await http_get("/api")
```

## Implementation

### Parser (`src/parser/src/parser.rs`)

Functions are parsed into `FunctionDef` AST nodes with parameters, return type, body, visibility, async flag, and decorators.

### Interpreter (`src/compiler/src/interpreter.rs`)

Functions are stored in a `HashMap<String, FunctionDef>` and invoked by:
1. Creating a new local environment
2. Binding parameters to argument values
3. Executing the body block
4. Returning the result

Closures capture their environment at definition time.

### Native Pipeline (TODO)

For native compilation:
1. HIR: Lower function definitions with typed parameters
2. MIR: Create function bodies with basic blocks
3. Cranelift: Generate function prologue/epilogue, call conventions

## Features Supported

| Feature | Interpreter | Native |
|---------|-------------|--------|
| Basic functions | Working | Stub |
| Parameters | Working | Stub |
| Return types | Working | Stub |
| Default params | Working | Stub |
| Closures | Working | Stub |
| Async functions | Working | Stub |
| Decorators | Partial | Stub |
| Recursion | Working | Stub |

## Tests

```bash
cargo test -p simple-driver interpreter_function
cargo test -p simple-driver interpreter_closure
cargo test -p simple-driver interpreter_recursion
cargo test -p simple-driver runner_handles_functions
```

## Files

- `src/compiler/src/interpreter.rs` — function registration and invocation
- `src/compiler/src/interpreter_call.rs` — call handling
- `src/driver/tests/runner_tests.rs` — function call coverage

## Known Issues

- Some decorator edge cases failing
- Native codegen not implemented

## Next Steps

1. HIR function lowering with type annotations
2. MIR basic block generation
3. Cranelift function codegen with proper calling convention
