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

## Specification Files

**Specifications live in two places:**

1. **Executable Specs:** `tests/specs/*_spec.spl` - Feature specifications with test cases
2. **Reference Docs:** `doc/spec/*.md` - Architecture, tooling, framework docs

**When to use each:**

- **Use _spec.spl** for:
  - Core language features with Feature IDs
  - Testable behavior and syntax
  - Examples that should compile and run
  - Feature validation and regression prevention

- **Use doc/spec/*.md** for:
  - Implementation architecture (parser, compiler)
  - Tooling specifications (formatter, linter, VSCode)
  - Framework documentation (BDD, GPU, 3D graphics)
  - Design rationale and high-level overviews

**Writing _spec.spl files:**
- See [doc/spec/SPEC_GUIDELINES.md](doc/spec/SPEC_GUIDELINES.md) for complete guide
- See [doc/spec/SPEC_QUICK_REF.md](doc/spec/SPEC_QUICK_REF.md) for quick reference
- Use docstrings for specification text
- Include executable test cases
- Link to Feature IDs in header metadata

**Migration in progress:**
- Status: [doc/spec/MIGRATION_STATUS.md](doc/spec/MIGRATION_STATUS.md)
- Full plan: [doc/SPEC_MIGRATION_PLAN.md](doc/SPEC_MIGRATION_PLAN.md)
- Migration script: `scripts/migrate_spec_to_spl.py`

## Recent Completions

### LLM-Friendly Features 100% Complete (2026-01-09)

Verified completion of all 40 LLM-friendly features (#880-919) with full capability-based effect system.

**Capability-Based Effects (#880-884):**
- `requires [cap1, cap2]` syntax in `__init__.spl` files
- Effect decorators: `@pure`, `@io`, `@net`, `@fs`, `@unsafe`, `@verify`, `@trusted`
- Module-level capability validation with inheritance
- Compile-time forbidden effect errors
- Stdlib annotations (17+ functions in host/async_nogc_mut/)

**Implementation:**
- `src/parser/src/ast/nodes/effects.rs` - Effect & Capability enums
- `src/parser/src/statements/module_system.rs` - parse_requires_capabilities()
- `src/compiler/src/module_resolver/manifest.rs` - validate_function_effects()
- `src/compiler/src/effects.rs` - Effect checking with operation lists
- `simple/std_lib/src/host/async_nogc_mut/` - Effect annotations

**AST/IR Export (#885-889):**
- `--emit-ast`, `--emit-hir`, `--emit-mir` flags
- `--error-format=json` for diagnostics
- Semantic diff via AST comparison

**Context Pack Generator (#890-893):**
- `simple context` command with markdown/JSON output
- Dependency symbol extraction via AST traversal
- 90% token reduction for LLM consumption

**Status:** 40/40 features complete (100%)

**Documentation:** See `doc/llm_friendly/LLM_FEATURES_100_COMPLETE_2026-01-09.md`

### Spec Migration Phase 2 Complete (2026-01-09)

Completed migration of all 15 core language specifications to executable test files.

**Phase 2 Results:**
- Category A (Direct): 7 files fully migrated (54.6K, 137 examples)
- Category B (Extract): 8 files extracted (72K, 157 examples)
- Total: 126.6K content, 294 code examples → test cases
- Success rate: 100% (15/15)

**Files Migrated/Extracted:**
- syntax, types, type_inference, async_default, suspension_operator, capability_effects, sandboxing
- functions, traits, memory, modules, data_structures, concurrency, macro, metaprogramming

**Tools Created:**
- `scripts/migrate_spec_to_spl.py` - Category A full migration
- `scripts/extract_tests_from_spec.py` - Category B extraction

**Organization:**
- All specs now in `tests/specs/*_spec.spl`
- Original Category A .md files marked "MIGRATED"
- Original Category B .md files marked "EXTRACTED" (kept as reference)
- Updated `doc/spec/README.md` with migration section
- Created `doc/spec/generated/` for future spec-gen output

**Timeline:** Phase 1+2 complete in 2 sessions (vs 3 weeks estimated)

**Status:** Phase 3 (Organization) in progress. Phases 4-5 pending.

**Documentation:** See `doc/SPEC_MIGRATION_PLAN.md` and `doc/spec/MIGRATION_STATUS.md`

### Spec Migration Planning Complete (2026-01-09)

Created comprehensive plan to migrate feature specifications from `doc/spec/*.md` to executable `tests/*_spec.spl` files.

**Analysis Results:**
- 60 spec files analyzed and categorized
- 7 files for direct migration (Category A - with Feature IDs)
- 8 files for extract + keep (Category B - large architectural specs)
- 45+ files to keep as reference (Category C/D - tooling, frameworks)

**Verification:**
- ✅ Comment-only .spl files compile successfully (no parser changes needed)
- Created test file: `tests/meta/comment_only_spec.spl`

**Deliverables:**
- `doc/SPEC_MIGRATION_PLAN.md` (535 lines) - Complete 6-week phased plan
- `doc/spec/MIGRATION_STATUS.md` (188 lines) - Quick reference summary
- `doc/spec/SPEC_GUIDELINES.md` (10K lines) - How to write _spec.spl files
- `doc/spec/SPEC_QUICK_REF.md` - Quick reference card
- `scripts/migrate_spec_to_spl.py` (12K lines) - Migration tool

**Migration Tool:**
```bash
# Dry run single file
python scripts/migrate_spec_to_spl.py --dry-run doc/spec/types.md tests/specs/types_spec.spl

# Migrate all Category A files
python scripts/migrate_spec_to_spl.py --all

# With verbose output
python scripts/migrate_spec_to_spl.py --all --verbose
```

**Status:** Planning phase complete, ready for Phase 1 execution (6-week timeline)

**Documentation:** See `doc/SPEC_MIGRATION_PLAN.md` and `doc/spec/SPEC_GUIDELINES.md`

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

