# Compiler Driver & Runner

*Source: `simple/std_lib/test/features/infrastructure/compiler_driver_spec.spl`*

---

# Compiler Driver & Runner

**Feature ID:** #106
**Category:** Infrastructure - Compiler Pipeline
**Difficulty:** 4/5
**Status:** Complete

## Overview

The Compiler Driver orchestrates the complete compilation pipeline from source code to
execution, managing multiple execution modes (interpreter, JIT, AOT) and cross-compilation
targets. The Runner component provides the high-level API for compiling and running Simple
programs.

Key components:
- **Runner:** High-level API for compilation and execution
- **ExecCore:** Core execution logic with mode selection
- **Compilation Modes:** Interpreter, JIT, AOT, SMF
- **Target Selection:** Native, cross-platform, embedded
- **Module Resolution:** Import handling and dependency tracking

## Key Features

- **Multi-Mode Execution:** Interpreter (fast startup), JIT (fast execution), AOT (production)
- **SMF Format:** Simple Module Format for pre-compiled binaries
- **Cross-Compilation:** Target different platforms from same source
- **Import Resolution:** Automatic module dependency handling
- **GC Integration:** Garbage collector lifecycle management
- **Incremental Compilation:** Module-level caching (planned)

## Implementation

**Primary Files:**
- `src/driver/src/runner.rs` - Runner API
- `src/driver/src/exec_core.rs` - Execution core
- `src/driver/src/interpreter.rs` - Interpreter mode

**Dependencies:**
- Feature #2: Parser
- Feature #100: Type Inference
- Feature #104: Dependency Tracker
- Feature #105: Native Loader

**Required By:**
- Simple CLI tool
- IDE integration
- Build system

## Execution Modes

### Interpreter Mode
Fast startup, full language support:
```simple
runner.run_file_interpreted("program.spl")
```

### SMF (Compiled) Mode
Pre-compiled binary execution:
```simple
# Compile
compiler.compile_to_smf("program.spl", "program.smf")

# Run
runner.run_smf("program.smf")
```

### JIT Mode (Planned)
Just-in-time compilation for hot code:
```simple
runner.run_file_jit("program.spl")
```

## Test Coverage

Validates compilation pipeline orchestration and execution modes.

**Implementation:** See `runner.rs::Runner`

**Given** Simple source file
        **When** compiling and running
        **Then** produces correct output

        **Verification:** Compilation works

**Given** compiled program
        **When** selecting execution mode
        **Then** runs in requested mode

        **Modes:**
        - Interpreter: Fast startup
        - SMF: Pre-compiled
        - JIT: Hot compilation

        **Verification:** Mode selection works

**Given** module with imports
        **When** compiling
        **Then** resolves dependencies

        **Example:**
        ```simple
        import crate.foo
        import crate.bar
        ```

        **Verification:** Import resolution works

**Given** circular imports
        **When** building dependency graph
        **Then** reports error

        **Verification:** Cycle detection works
