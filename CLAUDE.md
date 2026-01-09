# Simple Language Compiler - Development Guide

## Skills Reference

For detailed guidance, invoke with `/skill-name`:

| Skill | Purpose |
|-------|---------|
| `versioning` | Jujutsu (jj) workflow - **NOT git!** |
| `test` | Test writing (Rust & Simple BDD) |
| `sspec` | SSpec BDD framework, doc generation, coverage, duplication |
| `coding` | Coding standards, Simple language rules |
| `design` | Design patterns, type system, APIs |
| `architecture` | Compiler architecture, crate structure |
| `research` | Codebase exploration, documentation |
| `debug` | Debugging interpreter/codegen, tracing, GC logging |
| `stdlib` | Writing stdlib modules, variants, capabilities |
| `todo` | TODO/FIXME comment format |

Skills located in `.claude/skills/`.

---

## Key Features

- **LLM-Friendly**: IR export, context packs, lint framework (70% complete)
- **Pattern Matching Safety**: Exhaustiveness checking (5/5 complete)
- Memory model: Reference capabilities (`mut T`, `iso T`, `T`)
- Formatter/linter: `simple/app/`
- AOP & Unified Predicates: 19/51 features, 611 tests

---

## Critical Prohibitions

### Version Control
- ❌ **NEVER use git** - use `jj` (see `/versioning`)

### Scripts
- ❌ **NEVER write Python/Bash** - use Simple (`.spl`) only

### Tests
- ❌ **NEVER add `#[ignore]`** without user approval
- ❌ **NEVER skip failing tests** - fix or ask user

### Code Style
- ❌ **NEVER over-engineer** - only make requested changes
- ❌ **NEVER add unused code** - delete completely (no `_vars`)

---

## Documentation

**Bug Reports:** `simple/bug_report.md`
**Improvement Requests:** `simple/improve_request.md`
**Job Reports:** `doc/report/` (completion reports, session summaries)
**Feature Specs:** `doc/features/feature.md` - **read before implementing!**

---

## Quick Commands

```bash
make check         # fmt + lint + test (before commit)
make check-full    # + coverage + duplication
cargo test --workspace
./target/debug/simple script.spl
```

---

## Lean 4 Verification

```bash
./target/debug/simple --gen-lean module.spl --verify memory|types|effects|all
```

Projects in `verification/`: borrow checker, GC safety, effects, SC-DRF.

---

## Current Status

| Component | Status |
|-----------|--------|
| Lexer/Parser/AST | Complete |
| HIR/MIR | Complete (50+ instructions) |
| Codegen | Hybrid (Cranelift + Interpreter) |
| RuntimeValue | Complete (9 modules, 50+ FFI) |
| BDD Framework | Sprint 1 Complete + 21 Feature Specs |
| Test Count | 631+ tests |

---

## Postponed

**High:** LLM Features (#880-919), Test Framework, LSP
**Medium:** Test CLI, TUI Framework, Package Registry
**Blocked:** Generator JIT codegen

See `TODO.md` and `doc/features/done/` for archives.
