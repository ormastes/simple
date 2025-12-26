# Feature: Interpreter Interface

**Infrastructure Feature**
- **Importance**: 4/5
- **Difficulty**: 2/5
- **Status**: COMPLETED

## Goal

Provide a clean interface for running Simple code programmatically with I/O capture support.

## API

```rust
use simple_driver::interpreter::{run_code, Interpreter, RunResult, RunConfig};

// Simple usage
let result = run_code("main = 42", &[], "").unwrap();
assert_eq!(result.exit_code, 42);

// With configuration
let interpreter = Interpreter::new();
let result = interpreter.run(code, RunConfig {
    args: vec!["arg1".into()],
    stdin: "input".into(),
    timeout_ms: 5000,
}).unwrap();
```

## Files Created

| File | Purpose |
|------|---------|
| `src/driver/src/interpreter.rs` | Interpreter module with RunResult, RunConfig, Interpreter |
| `src/driver/tests/interpreter_tests.rs` | 21 system tests |
| `plans/14_interpreter_interface.md` | Implementation plan |

## Tests (21 total)

- `interpreter_runs_simple_code` - basic exit code
- `interpreter_returns_zero` - zero return
- `interpreter_arithmetic` - basic math
- `interpreter_arithmetic_complex` - complex expressions
- `interpreter_with_variables` - let bindings
- `interpreter_with_variable_expressions` - variable chains
- `interpreter_with_functions` - function calls
- `interpreter_with_nested_function_calls` - nested calls
- `interpreter_with_structs` - struct usage
- `interpreter_with_enums` - enum usage
- `interpreter_enum_comparison_false` - enum comparison
- `interpreter_if_else` - conditionals
- `interpreter_while_loop` - while loops
- `interpreter_for_loop` - for loops
- `interpreter_class_methods` - class methods
- `interpreter_error_handling_syntax` - syntax errors
- `interpreter_error_handling_undefined_variable` - undefined vars
- `interpreter_using_struct` - Interpreter struct
- `interpreter_with_config` - RunConfig usage
- `interpreter_run_with_stdin` - stdin helper
- `interpreter_result_has_empty_stdout` - stdout placeholder

## Progress

- [x] Create plan document (plans/14_interpreter_interface.md)
- [x] Create interpreter.rs with RunResult, RunConfig, Interpreter
- [x] Add run_code() convenience function
- [x] Export from driver/lib.rs
- [x] Create 21 system tests
- [x] Verify all tests pass (113 total workspace tests)

## Future Enhancements

- Actual stdout/stderr capture (when print/println builtins added)
- stdin consumption (when input() builtin added)
- Timeout enforcement
- Memory limits
