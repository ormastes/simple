# Declarative CLI Keyword — Support Matrix

**Date:** 2026-04-04
**Feature:** `cli Name:` declarative argument parser integrated into the language

## Feature Status: Implemented

The `cli Name:` keyword is a language-level declarative argument parser with full support across the interpreter and C backend compilation paths.

## Syntax Support

| Syntax Element | Status | Example |
|---------------|--------|---------|
| Bool flags | Implemented | `verbose = false` |
| String options | Implemented | `output = "out.txt"` |
| Int options | Implemented | `count = 0` |
| Short flags | Implemented | `-v verbose = false` |
| Docstrings | Implemented | `"""Description"""` |
| Default values | Implemented | `= "default"` |
| File extension detection | Implemented | `file: ".spl"` |
| Prefetch directive | Implemented | `prefetch: true` |
| Default subcommand | Implemented | `default: .repl` |
| Subcommands (with body) | Implemented | `sub build: ...` |
| Subcommands (passthrough) | Implemented | `sub lint, fmt, fix` |
| Generated `--help` | Implemented | Automatic from docstrings |
| Generated struct | Implemented | `Args.field_name` access |

## Backend Support

| Component | Status | File |
|-----------|--------|------|
| Parser | Implemented | `src/compiler/10.frontend/core/parser_cli.spl` |
| AST node (DECL_CLI) | Implemented | `src/compiler/10.frontend/core/ast.spl` |
| Interpreter eval | Implemented | `src/compiler/10.frontend/core/interpreter/cli_eval.spl` |
| C backend codegen | Implemented | `src/compiler/70.backend/backend/cli_codegen.spl` |
| LLVM backend | Not yet | Needs MIR-level lowering |
| Cranelift backend | Not yet | Needs MIR-level lowering |
| WASM backend | Not yet | Needs MIR-level lowering |

## Codegen Properties (C Backend)

- O(1) switch-tree parser via `switch(klen) { case N: memcmp... }`
- Short flag handling with `-k value` and `-kvalue` forms
- `--key=value` splitting
- Static help text generation from docstrings
- File extension detection for positional arguments
- Type-safe struct with typed fields

## Test Coverage

35+ test specification files covering:
- Basic args, defaults, types, inference
- Short flags, error handling, help generation
- Subcommand dispatch, migration patterns
- System-level CLI integration
- Performance smoke tests (startup + arg parsing)
- Codegen unit tests

## Adoption Status

| Scope | Status |
|-------|--------|
| Language feature | Implemented |
| Migration demo (`main_cli_migration.spl`) | Available |
| Design doc (`doc/05_design/cli_args_design.md`) | Complete (700 lines) |
| Production adoption (main.spl) | Planned (migration reduces ~105 lines) |
| Per-app adoption (66 commands) | Planned follow-on |

## Error Codes (Planned)

| Code | Description | Status |
|------|------------|--------|
| E-CLI-001 | Duplicate option name | Planned |
| E-CLI-002 | Reserved short flag | Planned |
| E-CLI-003 | Type inference failure | Planned |
| E-CLI-004 | Invalid default value | Planned |
| E-CLI-005 | Duplicate subcommand | Planned |
| E-CLI-006 | Conflicting short flags | Planned |
| E-CLI-007 | Missing required option | Planned |
