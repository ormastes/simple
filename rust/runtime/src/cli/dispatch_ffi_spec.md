# Rust FFI Handler Implementation Specification

**File:** `rust/runtime/src/cli/dispatch.rs` (to be created)
**Purpose:** Implement `rt_cli_dispatch_rust` FFI function for command fallback
**Phase:** 1C - Benchmarking and Rust FFI Handler

## Overview

This document specifies the Rust FFI handler that receives command dispatch requests from Simple and routes them to the appropriate Rust command handlers.

## Function Signature

```rust
#[no_mangle]
pub extern "C" fn rt_cli_dispatch_rust(
    cmd: &str,
    args: &[String],
    gc_log: bool,
    gc_off: bool
) -> i64
```

**Parameters:**
- `cmd` - Command name (e.g., "compile", "check", "test")
- `args` - Full command-line arguments including command name
- `gc_log` - Enable GC logging
- `gc_off` - Disable GC

**Returns:**
- Exit code (0 = success, non-zero = error)

## Implementation Template

```rust
// rust/runtime/src/cli/dispatch.rs

use simple_driver::cli;

/// Dispatch a command to its Rust handler.
///
/// This is called from Simple's dispatch system when:
/// - Simple implementation doesn't exist
/// - Simple implementation fails to load
/// - Environment variable forces Rust (SIMPLE_*_RUST=1)
/// - Special flags require Rust implementation
#[no_mangle]
pub extern "C" fn rt_cli_dispatch_rust(
    cmd: &str,
    args: &[String],
    gc_log: bool,
    gc_off: bool
) -> i64 {
    match cmd {
        // Compilation commands
        "compile" => cli::compile::handle_compile(args),
        "targets" => cli::commands::handle_targets() as i64,
        "linkers" => cli::commands::handle_linkers() as i64,
        "check" => cli::check::handle_check(args),

        // Code quality
        "lint" => cli::code_quality::run_lint(args) as i64,
        "fix" => cli::code_quality::run_lint(args) as i64,  // Same handler
        "fmt" => cli::code_quality::run_fmt(args) as i64,

        // Testing
        "test" => cli::test_runner::handle_test_rust(args, gc_log, gc_off) as i64,

        // Web framework
        "web" => cli::commands::handle_web(args),

        // File watching
        "watch" => {
            if args.len() < 2 {
                eprintln!("error: watch requires a source file");
                return 1;
            }
            cli::basic::watch_file(&args[1].into())
        }

        // Localization
        "i18n" => cli::i18n::run_i18n(args),

        // Migration and tooling
        "migrate" => cli::migrate::run_migrate(args),
        "mcp" => cli::llm_tools::run_mcp(args),
        "diff" => cli::llm_tools::run_diff(args),
        "context" => cli::llm_tools::run_context(args),
        "constr" => cli::llm_tools::run_constr(args),

        // Analysis and querying
        "query" => cli::analysis::run_query(args),
        "info" => cli::analysis::run_info(args),
        "spec-coverage" => cli::audit::run_spec_coverage(args),
        "replay" => cli::audit::run_replay(args),

        // Code generation
        "gen-lean" => cli::gen_lean::run_gen_lean(args),
        "feature-gen" => cli::doc_gen::run_feature_gen(args),
        "task-gen" => cli::doc_gen::run_task_gen(args),
        "spec-gen" => cli::doc_gen::run_spec_gen(args),
        "todo-scan" => cli::doc_gen::run_todo_scan(args),
        "todo-gen" => cli::doc_gen::run_todo_gen(args),
        "sspec-docgen" => cli::sspec_docgen::run_sspec_docgen(args),

        // Documentation
        "brief" => cli::commands::handle_brief(args),
        "dashboard" => cli::commands::handle_dashboard(args),

        // Package management
        "init" => cli::commands::handle_init(args),
        "install" => cli::commands::handle_install() as i64,
        "publish" => cli::commands::handle_publish(args),
        "add" => cli::commands::handle_add(args),
        "remove" => cli::commands::handle_remove(args),
        "search" => cli::commands::handle_search(args),
        "deps" => cli::commands::handle_deps(args),
        "list" => cli::commands::handle_list() as i64,
        "tree" => cli::commands::handle_tree() as i64,

        // Build system
        "build" => cli::commands::handle_build(args),
        "run" => cli::commands::handle_run(args, gc_log, gc_off),
        "clean" => cli::commands::handle_clean(args),

        // Benchmarking
        "bench" => cli::commands::handle_bench(args),

        // REPL and execution
        "repl" => cli::repl::run_repl(gc_log, gc_off) as i64,
        "verify" => cli::verify::run_verify(args),

        // Qualification
        "qualify-ignore" => cli::qualify_ignore::handle_qualify_ignore_wrapper(args),

        // Unknown command
        _ => {
            eprintln!("error: unknown command: {}", cmd);
            eprintln!("Run 'simple --help' for usage information");
            1
        }
    }
}
```

## Integration Steps

### 1. Create the file

```bash
# Create dispatch.rs in runtime
touch rust/runtime/src/cli/dispatch.rs
```

### 2. Add module declaration

In `rust/runtime/src/cli/mod.rs`:
```rust
pub mod dispatch;
```

If `cli` module doesn't exist, create it:
```rust
// rust/runtime/src/lib.rs
pub mod cli;
```

### 3. Import required modules

At the top of `dispatch.rs`:
```rust
use simple_driver::cli::{
    compile, check, code_quality, test_runner, basic,
    i18n, migrate, llm_tools, analysis, audit,
    gen_lean, doc_gen, sspec_docgen, repl, verify,
    qualify_ignore, commands
};
```

### 4. Build and verify

```bash
# Build runtime with new FFI function
cd rust/runtime
cargo build --release

# Verify symbol is exported
nm -D target/release/libsimple_runtime.so | grep rt_cli_dispatch_rust
# Should show: ... T rt_cli_dispatch_rust
```

## Testing

### Unit Test

Add to `rust/runtime/src/cli/dispatch.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dispatch_help() {
        let args = vec!["simple".to_string(), "--help".to_string()];
        let code = rt_cli_dispatch_rust("--help", &args, false, false);
        assert_eq!(code, 0);
    }

    #[test]
    fn test_dispatch_unknown_command() {
        let args = vec!["simple".to_string(), "invalid-cmd".to_string()];
        let code = rt_cli_dispatch_rust("invalid-cmd", &args, false, false);
        assert_eq!(code, 1);
    }

    #[test]
    fn test_dispatch_compile() {
        let args = vec!["simple".to_string(), "compile".to_string(), "--help".to_string()];
        let code = rt_cli_dispatch_rust("compile", &args, false, false);
        assert_eq!(code, 0);
    }
}
```

### Integration Test

Run Simple integration tests:

```bash
# Run dispatch tests
simple test test/integration/cli_dispatch_spec.spl

# Expected: 23 tests pass
```

## Performance Considerations

### Return Value Optimization

The function returns `i64` directly (not `Result`) to minimize FFI overhead:

```rust
// Good: Direct return
pub extern "C" fn rt_cli_dispatch_rust(...) -> i64 {
    match cmd {
        "compile" => handle_compile(args),  // Returns i64
        _ => 1
    }
}

// Bad: Unnecessary Result
pub extern "C" fn rt_cli_dispatch_rust(...) -> Result<i64, String> {
    // Adds overhead for Result marshalling
}
```

### Command String Optimization

Use `&str` (not `String`) for the command parameter:

```rust
// Good: Borrows string (zero-copy)
pub extern "C" fn rt_cli_dispatch_rust(cmd: &str, ...) -> i64

// Bad: Owns string (copies data)
pub extern "C" fn rt_cli_dispatch_rust(cmd: String, ...) -> i64
```

### Match Statement Optimization

The match statement compiles to a jump table (O(1) lookup):

```rust
match cmd {
    "compile" => handler1(),
    "check" => handler2(),
    // ... 48 branches
}
// Compiler optimizes to hash table or binary search
// Time complexity: O(1) or O(log n)
```

## Error Handling

### Command Not Found

```rust
_ => {
    eprintln!("error: unknown command: {}", cmd);
    eprintln!("Run 'simple --help' for usage information");
    1  // Exit code 1
}
```

### Handler Panics

Rust handlers may panic. Consider adding panic catching:

```rust
use std::panic;

pub extern "C" fn rt_cli_dispatch_rust(...) -> i64 {
    let result = panic::catch_unwind(|| {
        match cmd {
            "compile" => handle_compile(args),
            // ... other commands
        }
    });

    match result {
        Ok(code) => code,
        Err(e) => {
            eprintln!("error: command '{}' panicked: {:?}", cmd, e);
            -1  // Internal error
        }
    }
}
```

## Verification Checklist

- [ ] File created: `rust/runtime/src/cli/dispatch.rs`
- [ ] Module declared in `rust/runtime/src/cli/mod.rs`
- [ ] All 48 commands have match branches
- [ ] Unknown command handler implemented
- [ ] Unit tests pass
- [ ] Integration tests pass (`test/integration/cli_dispatch_spec.spl`)
- [ ] Symbol exported: `nm -D` shows `rt_cli_dispatch_rust`
- [ ] Benchmarks run without errors

## Expected Results

After implementation:

1. **All commands route correctly**
   - Environment overrides work (`SIMPLE_*_RUST=1`)
   - Special flags trigger Rust handlers
   - Unknown commands show error message

2. **Performance meets targets**
   - Dispatch overhead <10ms
   - Startup time <25ms
   - Total time within 2x of current Rust

3. **Tests pass**
   - 23 integration tests pass
   - 3 unit tests pass
   - Zero regressions

## Next Steps After Implementation

1. **Run benchmarks:**
   ```bash
   simple test test/benchmarks/cli_dispatch_perf_spec.spl
   ```

2. **Profile if needed:**
   ```bash
   perf record -g simple compile --help
   perf report
   ```

3. **Optimize hotspots:**
   - Lazy module loading
   - SMF precompilation
   - Binary embedding

4. **Phase 1D: Main CLI integration**
   - Update `src/app/cli/main.spl` to use dispatch system
   - Run differential tests (Simple vs Rust)
   - Verify zero regressions

## Related Files

- `src/app/cli/dispatch.spl` - Simple dispatch system
- `src/app/io/mod.spl` - FFI declarations
- `test/integration/cli_dispatch_spec.spl` - Integration tests
- `test/benchmarks/cli_dispatch_perf_spec.spl` - Performance benchmarks
- `rust/driver/src/main.rs` - Original Rust dispatch (reference)
