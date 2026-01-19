# Simple Language Compiler - Development Guide

## Skills Reference

For detailed guidance, invoke with `/skill-name`:

| Skill | Purpose |
|-------|---------|
| `versioning` | Jujutsu (jj) workflow - **NOT git!** |
| `test` | Test writing (Rust & Simple BDD) |
| `sspec` | **SSpec BDD framework** - Testing → Doc generation workflow |
| `coding` | Coding standards, Simple language rules |
| `design` | Design patterns, type system, APIs |
| `architecture` | Compiler architecture, crate structure |
| `research` | Codebase exploration, documentation |
| `debug` | Debugging interpreter/codegen, tracing, GC logging |
| `stdlib` | Writing stdlib modules, variants, capabilities |
| `todo` | TODO/FIXME comment format |
| `doc` | Documentation writing: specs (SSpec), research, design, guides |

Skills located in `.claude/skills/`.

**Writing SSpec Tests:**
- **Template:** `.claude/templates/sspec_template.spl` - Copy this for new specs
- **Complete Example:** `doc/guide/sspec_complete_example.md` - Full workflow
- **Quick Start:** `/sspec` skill or `cat .claude/skills/sspec.md`

---

## Key Features

- **LLM-Friendly**: IR export, context packs, lint framework (75% complete)
  - **New Lints**: `print_in_test_spec`, `todo_format`
- **Pattern Matching Safety**: Exhaustiveness checking (5/5 complete)
- **Scala-Style Syntax**: `val`/`var` variables, implicit `self` in methods
- Memory model: Reference capabilities (`mut T`, `iso T`, `T`)
- Formatter/linter: `simple/app/`
- AOP & Unified Predicates: 19/51 features, 611 tests

---

## Syntax Quick Reference

**Variables:**
```simple
val name = "Alice"    # Immutable (preferred)
var count = 0         # Mutable
```

**Implicit val/var (type inference, future/experimental):**
```simple
name = "Alice"        # Implicit val (immutable)
count_ = 0            # Implicit var (mutable, trailing underscore)
```

**Generics (use `<>` not `[]`):**
```simple
# Template/wrapper types - use angle brackets (for libraries)
fn map<T, U>(f: fn(T) -> U) -> U
struct Container<T>
Option<T>, Result<T, E>, List<Int>

# Arrays - use square brackets
[i32]           # array type
[1, 2, 3]       # array literal
arr[0]          # indexing

# Prefer type inference in app code
fn double(x):             # Types inferred from usage
    x * 2
fn add(a, b):             # No explicit generics needed
    a + b
```

**Implicit return:**
```simple
fn square(x):
    x * x                     # Last expression is returned (preferred)

fn explicit_return(x):
    return x * x              # Use only when needed for clarity
```

**Collection methods:**
```simple
items.map(\x: x * 2)          # Transform each element
items.filter(\x: x > 5)       # Keep matching elements
list1.merge(list2)            # Combine collections
```

**Ranges and comprehensions:**
```simple
0..10                         # Exclusive range: 0 to 9
0..=10                        # Inclusive range: 0 to 10
[for x in 0..20 if x % 2 == 0: x]   # List comprehension with filter
```

**Methods (LL(1)-friendly, implicit self):**
```simple
impl MyStruct:
    static fn new() -> MyStruct:        # Static method (no self)
    fn get_value() -> i32:              # Immutable method (self implicit)
    me set_value(v: i32):               # Mutable method ('me' keyword, self implicit)
```

See `/coding` skill for full details.

---

## Critical Prohibitions

### Version Control
- ❌ **NEVER use git** - use `jj` (see `/versioning`)
- ❌ **NEVER create branches** - work directly on `main`
- ✅ Always use `jj bookmark set main -r @` then `jj git push --bookmark main`

### Scripts
- ❌ **NEVER write Python/Bash** - use Simple (`.spl`) only

### Tests
- ❌ **NEVER add `#[ignore]`** without user approval
- ❌ **NEVER skip failing tests** - fix or ask user

### Code Style
- ❌ **NEVER over-engineer** - only make requested changes
- ❌ **NEVER add unused code** - delete completely (no `_vars`)

### Generic Syntax
- ✅ **USE `<>` for generics**: `Option<T>`, `List<Int>`, `fn map<T, U>`
- ❌ **DEPRECATED `[]` syntax**: `Option[T]` will show compiler warning
- 🔧 **Auto-migrate**: Run `simple migrate --fix-generics src/` (Note: tool needs refinement)
- 📅 **Timeline**: Deprecation warnings active, `[]` will be removed in v1.0.0

### Question Mark (`?`) Usage
- ❌ **NEVER use `?` in method/function/variable names** - unlike Ruby
- ✅ **`?` is an operator only**: try operator (`result?`), optional type (`T?`)
- ✅ **Use `is_*` prefix for predicates**: `is_empty()`, `is_valid()`, `is_some()`
- 📖 **Design Decision**: See `doc/design/question_mark_design_decision.md`

### TODO Comments
- ❌ **NEVER remove TODO markers** unless the feature is fully implemented and working
- ✅ Can add documentation/implementation notes to existing TODOs
- ✅ Only delete TODO comment when code implementing that feature is complete
- 📊 **Status**: See `doc/report/todo_status_2026-01-16.md`

---

## Documentation

**Bug Reports:** `simple/bug_report.md`
**Improvement Requests:** `simple/improve_request.md`
**Job Reports:** `doc/report/` (completion reports, session summaries)
**Feature Specs:** `simple/std_lib/test/features/` - **Executable SSpec tests (see `/doc` skill)**
**Research:** `doc/research/` (investigation, design exploration)
**Guides:** `doc/guide/` (user-facing tutorials)

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
