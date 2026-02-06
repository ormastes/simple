# Simple Language Interpreter (Self-Hosted)

This is the self-hosted interpreter for the Simple programming language.
It is written in Simple and can interpret itself.

## Status: Scaffolding Complete

This is a complete scaffolding/skeleton for the future self-hosted interpreter.
All module structures are in place with stub implementations that show the intended
architecture. The actual logic will be completed as part of the self-hosting effort.

**Current stats:** 26 files, ~3,200 lines of scaffolding code.

## Architecture

```
interpreter/
├── main.spl              # CLI entry point (~100 lines)
├── core/
│   ├── __init__.spl      # Core module exports
│   ├── eval.spl          # Main evaluation loop (~400 lines)
│   ├── environment.spl   # Variable bindings (~200 lines)
│   └── value.spl         # Runtime values (~300 lines)
├── expr/
│   ├── __init__.spl      # Expression evaluation entry
│   ├── literals.spl      # Literals: Int, String, Bool, etc. (~150 lines)
│   ├── arithmetic.spl    # Binary ops: +, -, *, /, % (~200 lines)
│   ├── comparison.spl    # Comparison: ==, !=, <, >, etc. (~150 lines)
│   ├── logical.spl       # Logical: and, or, not (~100 lines)
│   ├── collections.spl   # Array, Dict, Tuple (~250 lines)
│   ├── indexing.spl      # Index, slice operations (~200 lines)
│   └── calls.spl         # Function/method calls (~300 lines)
├── control/
│   ├── __init__.spl      # Control flow exports
│   ├── conditional.spl   # if/elif/else (~150 lines)
│   ├── match.spl         # Pattern matching (~300 lines)
│   └── loops.spl         # for, while, loop (~250 lines)
├── async_runtime/
│   ├── __init__.spl      # Async runtime exports
│   ├── futures.spl       # async/await (~250 lines)
│   ├── actors.spl        # Actor spawn/send/recv (~200 lines)
│   └── generators.spl    # yield, generator state (~200 lines)
├── ffi/
│   ├── __init__.spl      # FFI exports
│   ├── bridge.spl        # FFI to compiled code (~300 lines)
│   ├── builtins.spl      # Built-in functions (~200 lines)
│   └── extern.spl        # External bindings (~150 lines)
└── helpers/
    ├── __init__.spl      # Helper exports
    ├── macros.spl        # Macro expansion (~250 lines)
    ├── imports.spl       # Import resolution (~150 lines)
    └── debug.spl         # Debugging support (~100 lines)
```

## Current Size

~3,200 lines scaffolding (26 files)
Target: ~5,000-6,000 lines when complete

## Migration Strategy

1. **Phase 1:** Core evaluation (eval.spl, environment.spl, value.spl)
2. **Phase 2:** Expression handling (all expr/*.spl)
3. **Phase 3:** Control flow (all control/*.spl)
4. **Phase 4:** Async runtime (all async_runtime/*.spl)
5. **Phase 5:** FFI bridge + helpers

## Bootstrap Approach

- Keep Rust interpreter for compiling Simple interpreter (chicken/egg)
- Simple interpreter can interpret itself once complete
- Rust interpreter becomes fallback/bootstrap only

## Usage (when complete)

```bash
# Run a script
./simple_interpret script.spl arg1 arg2

# Start REPL
./simple_interpret --repl

# Evaluate expression
./simple_interpret --eval "1 + 2 * 3"
```

## Building

```bash
# Build with Rust compiler
./target/debug/simple --compile simple/app/interpreter/main.spl -o simple/bin_simple/simple_interpret

# Or use build script
cd simple && ./build_tools.sh interpreter
```
