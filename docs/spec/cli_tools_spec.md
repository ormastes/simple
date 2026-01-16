# CLI Tools & Utilities

*Source: `simple/std_lib/test/features/infrastructure/cli_tools_spec.spl`*

---

# CLI Tools & Utilities

**Feature ID:** #109
**Category:** Infrastructure - Developer Tools
**Difficulty:** 2/5
**Status:** Complete

## Overview

The CLI Tools provide developer utilities for LLM-friendly workflows, code analysis,
automated migration, code generation, and debugging support.

## Key Features

- **LLM Tools:** Context packs, IR export, lint framework (75% complete)
- **Analysis Tools:** Dependency graphs, duplication detection
- **Migration Tools:** SSpec migration, generic syntax migration
- **Code Generation:** Diagram generation, scaffolding
- **Debugging:** Sandbox mode, verbose logging, tracing

## Implementation

**Primary Files:**
- `src/driver/src/cli/*.rs` - CLI tool implementations
- `src/driver/src/cli/basic.rs` - Basic CLI commands
- `src/driver/src/cli/compile.rs` - Compilation commands
- `src/driver/src/cli/doc_gen.rs` - Documentation generation
- `src/driver/src/cli/gen_lean.rs` - Lean 4 code generation
- `src/driver/src/cli/test_runner.rs` - Test execution

## Key Tools

### LLM-Friendly Features
- **Context Packs:** Bundle codebase for LLM context
- **IR Export:** Export intermediate representation
- **Lint Framework:** 75% complete (print_in_test_spec, todo_format lints)

### Analysis Tools
- **Dependency Graphs:** Visualize module dependencies
- **Duplication Detection:** Find duplicated code blocks
- **Complexity Analysis:** Measure code complexity

### Migration Tools
- **SSpec Migration:** Convert old test format to new
- **Generic Syntax Migration:** Convert `[]` to `<>` for generics

### Code Generation
- **Diagram Generation:** Generate architecture diagrams
- **Scaffolding:** Create project templates
- **Lean Export:** Generate Lean 4 verification code

### Debugging Tools
- **Sandbox Mode:** Isolated execution environment
- **Verbose Logging:** Detailed execution traces
- **GC Logging:** Garbage collection events

## Test Coverage

Validates CLI tool functionality.

**Given** Simple source code
        **When** exporting IR
        **Then** produces LLM-friendly representation

        **Verification:** IR export works

**Given** codebase
        **When** creating context pack
        **Then** bundles relevant files

        **Verification:** Context pack generation works

**Given** codebase
        **When** running duplication detector
        **Then** finds duplicated blocks

        **Verification:** Duplication detection works

**Given** module imports
        **When** generating dependency graph
        **Then** visualizes dependencies

        **Verification:** Dependency graphs work

**Given** old generic syntax `Option[T]`
        **When** running migration tool
        **Then** converts to `Option<T>`

        **Example:**
        ```
        Before: List[Int]
        After:  List<Int>
        ```

        **Verification:** Generic syntax migration works

**Given** Simple code
        **When** generating Lean export
        **Then** produces Lean 4 code

        **Verification:** Lean export works

**Given** SSpec files
        **When** running doc generator
        **Then** produces markdown docs

        **Verification:** Doc generation works
