# Declarative Argparser Completion Report

**Date:** 2026-04-04
**Feature:** `cli Name:` — declarative argument parsing integrated into the Simple language
**Status:** Implemented

## Summary

The `cli Name:` keyword provides language-level declarative argument parsing with full support across interpreter mode and C backend compilation. The feature includes parsing, AST representation, interpreter evaluation, C backend codegen, and comprehensive test coverage.

## Implementation Stack

| Layer | File | Status |
|-------|------|--------|
| Parser | `src/compiler/10.frontend/core/parser_cli.spl` | Complete |
| AST | `src/compiler/10.frontend/core/ast.spl` (DECL_CLI = 13) | Complete |
| Interpreter | `src/compiler/10.frontend/core/interpreter/cli_eval.spl` | Complete |
| C Codegen | `src/compiler/70.backend/backend/cli_codegen.spl` | Complete |
| Runtime lib | `src/lib/nogc_sync_mut/cli/cli_parser.spl` | Complete (builder API) |
| Design doc | `doc/05_design/cli_args_design.md` | Complete (700 lines) |
| Migration demo | `src/app/cli/main_cli_migration.spl` | Available |

## Key Capabilities

1. **Declarative syntax**: `cli Args:` blocks define options, flags, subcommands with docstrings
2. **Type inference**: bool/string/int/float inferred from default values
3. **Short flags**: `-v verbose = false` generates both `--verbose` and `-v`
4. **Subcommands**: `sub build:` with body or `sub lint, fmt, fix` passthrough
5. **File detection**: `file: ".spl"` enables positional file argument with extension check
6. **Help generation**: `--help` automatically generated from docstrings
7. **O(1) dispatch**: C codegen produces switch-tree parser (no string scanning loops)

## Test Coverage

| Category | Files | Status |
|----------|-------|--------|
| Basic args | `test/feature/usage/cli_args_basic_spec.spl` | Active |
| Default values | `test/feature/usage/cli_args_default_spec.spl` | Active |
| File detection | `test/feature/usage/cli_args_file_spec.spl` | Active |
| Help generation | `test/feature/usage/cli_args_help_spec.spl` | Active |
| Type inference | `test/feature/usage/cli_args_inference_spec.spl` | Active |
| Short flags | `test/feature/usage/cli_args_short_spec.spl` | Active |
| Subcommands | `test/feature/usage/cli_args_subcommand_spec.spl` | Active |
| Type system | `test/feature/usage/cli_args_types_spec.spl` | Active |
| Error handling | `test/feature/usage/cli_args_error_spec.spl` | Active |
| Migration | `test/feature/usage/cli_args_migration_spec.spl` | Active |
| Codegen unit | `test/unit/app/cli/cli_codegen_spec.spl` | Active |
| Validation | `test/unit/app/cli/cli_validation_spec.spl` | Active |
| System | `test/system/infrastructure/cli_system_spec.spl` | Active |
| Dispatch | `test/integration/app/cli_dispatch_spec.spl` | Active |
| Perf | `test/integration/app/startup_argparse_mmap_perf_spec.spl` | Active |
| **Total** | **35+ files** | |

## Proof Evidence

`test/integration/app/startup_argparse_mmap_perf_spec.spl` provides end-to-end proof:
1. Writes a `cli Args:` source file dynamically
2. Compiles it with the Simple compiler
3. Executes the compiled binary with arguments
4. Verifies parsed values in output

## Status Promotion

- **Before:** "Partial but real" — parser, eval, codegen exist but not the uniform CLI path
- **After:** "Implemented" — language feature fully operational with comprehensive tests

## Follow-on Work (Not Blocking)

1. **Production adoption**: Migrate `main.spl` GlobalFlags to `cli Args:` (saves ~105 lines)
2. **Per-app migration**: 66 CLI commands can adopt `cli Name:` incrementally
3. **LLVM/Cranelift/WASM backends**: Need MIR-level lowering (currently interpreter + C only)
4. **Error codes E-CLI-001 to E-CLI-007**: Validation rules from design doc

## Support Matrix

See `doc/04_architecture/cli_keyword_support_matrix.md` for detailed capability table.
