# AGENTS

This file documents guidance for AI agents working on the Simple compiler repository.

## Version Control

**This project uses Jujutsu (jj), not Git.**

- **DO NOT** use `git commit`, `git push`, `git pull`
- **USE** `jj commit`, `jj git push`, `jj git fetch`
- **Snapshots:** jj automatically creates snapshots on file changes
- **Branches:** Use `jj branch set <name>` instead of `git checkout -b`
- **Push:** Use `jj git push` to push to origin

**Basic Workflow:**
```bash
# Check status
jj status

# Create snapshot with message
jj commit -m "message"

# Push to remote
jj git push
```

**Learn more:** See `doc/plans/27_jj_integration.md` for full JJ integration details.

## Recent Completions

### AST/HIR/MIR Export Complete (2025-12-24)

Completed IR export functionality for LLM-friendly compiler introspection (#885-887).

**Implementation:**
- `src/compiler/src/ir_export.rs` - JSON export for AST, HIR, MIR
- `src/compiler/src/pipeline/core.rs` - Emit options in CompilerPipeline
- `src/compiler/src/pipeline/execution.rs` - AST emission point
- `src/compiler/src/pipeline/lowering.rs` - HIR/MIR emission points
- `src/driver/src/exec_core.rs` - compile_with_options methods
- `src/driver/src/runner.rs` - Public API with options
- `src/driver/src/main.rs` - CLI integration

**Key Features:**
- `--emit-ast[=file]` - Export AST to file or stdout
- `--emit-hir[=file]` - Export HIR to file or stdout (native path only)
- `--emit-mir[=file]` - Export MIR to file or stdout (native path only)
- JSON format with pretty-printing
- Minimal changes to existing pipeline

**Status:** AST/IR Export category now 80% complete (4/5 features)

**Documentation:** See `doc/llm_friendly/ast_hir_mir_export.md`

### LLM-Friendly Features Status (2025-12-24)

Assessed implementation status of LLM-Friendly Features (#880-919) - **14/40 complete (35%)**.

**Completed Categories:**
- AST/IR Export: 80% (4/5 features) - `--emit-ast`, `--emit-hir`, `--emit-mir`, `--error-format=json`
- Context Pack Generator: 75% (3/4 features) - `simple context` command with markdown/JSON output
- Lint Framework: 60% (3/5 features) - Lint rule trait, built-in rules, configurable severity

**Next Priorities:**
1. Complete AST/IR Export (#889 - Semantic diff tool)
2. Complete Context Pack (#891 - Dependency symbol extraction)
3. Complete Lint Framework (#906-907 - CLI command + auto-fix)
4. Implement Canonical Formatter (#908-910)

**Documentation:** See `doc/llm_friendly/implementation_status.md`

### Type System Enhancements (2025-12-23)

Implemented tagged unions (algebraic data types) and bitfields (#1330-1339).

**Implementation:**
- `src/type/src/tagged_union.rs` - TaggedUnion and UnionVariant types
- `src/type/src/bitfield.rs` - Bitfield types with automatic layout
- Extended `Type` enum with `TaggedUnion(String)` and `Bitfield(String)` variants

**Key Features:**
- Tagged unions with discriminants for pattern matching
- Generic union support (e.g., `Option<T>`, `Result<T,E>`)
- Exhaustiveness checking for match expressions
- Bitfield types with automatic offset calculation
- Support for 8-128 bit backing types (u8, u16, u32, u64, u128)
- FFI-compatible layouts

**Tests:** 10 comprehensive unit tests (3 for unions, 7 for bitfields)

**Documentation:** See `doc/TYPE_SYSTEM_ENHANCEMENT.md` for full details.

## Development Guidelines

When working on type system features:

1. **Add new type variants** in `src/type/src/lib.rs` Type enum
2. **Create separate modules** for complex types (see `tagged_union.rs`, `bitfield.rs`)
3. **Include comprehensive tests** - aim for 3-7 unit tests per module
4. **Update substitution logic** in `Type::apply_subst()` for new variants
5. **Update `contains_var()`** for new variants that may contain type variables
6. **Export public API** through module declarations and `pub use`

## Testing Strategy

- Unit tests go in the same file (in `#[cfg(test)] mod tests`)
- Integration tests in `tests/` directory
- Run type tests: `cargo test -p simple-type`
- Run all tests: `make test`

