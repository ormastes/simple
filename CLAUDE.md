# Simple Language Compiler - Development Guide
Impl in simple unless it has big performance differences.

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

**Full Syntax Reference:** `doc/guide/syntax_quick_reference.md` - Complete syntax guide with all features

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

**Slicing and indexing:**
```simple
arr[0]                        # First element
arr[-1]                       # Last element (negative indexing)
arr[-2]                       # Second to last
arr[1:4]                      # Slice from index 1 to 3
arr[:3]                       # First 3 elements
arr[2:]                       # From index 2 to end
arr[::2]                      # Every other element (step=2)
arr[::-1]                     # Reversed
"Hello"[1:4]                  # String slicing: "ell"
```

**Optional chaining and null coalescing:**
```simple
user?.name                    # Returns None if user is None
user?.profile?.settings       # Chain safe navigation
obj?.method()                 # Safe method call
user?.name ?? "Anonymous"     # Default if None
config["key"] ?? default      # Fallback value
```

**Strings:**
```simple
print "Hello, {name}!"        # Interpolation is default (no f"" needed)
print "Result: {x + y}"       # Expressions in braces
print r"regex: \d+{3}"        # Raw string (no interpolation, no escapes)
```

**Format String Templates (Future):**
```simple
# Template with auto-detected const keys
val template = "Welcome {user} to {city}"

# Instantiate with dict - keys auto-validated at compile time
val greeting = template.with {"user": username, "city": current_city}

# Compile errors for wrong keys (no type annotation needed):
val bad = template.with {"usr": x}   # ERROR: "usr" not in ["user", "city"]
val missing = template.with {"user": x}  # ERROR: Missing key "city"
```

**Constructors:**

**Core Rule:** Use direct construction `ClassName(field: value)` - that's it!

```simple
struct Point:
    x: i64
    y: i64

class StringInterner:
    strings: Dict<text, i32>
    reverse: Dict<i32, text>
    next_id: i32

# ✅ PRIMARY: Direct construction (no method needed)
val p = Point(x: 3, y: 4)
val interner = StringInterner(strings: {}, reverse: {}, next_id: 0)
```

**Optional: Custom factory methods (for special cases)**

When you need special initialization logic, use `static fn` with a descriptive name:

```simple
impl Point:
    # ✅ Named factory for common case
    static fn origin() -> Point:
        Point(x: 0, y: 0)

    # ✅ Named factory for special transformation
    static fn from_polar(r: f64, theta: f64) -> Point:
        Point(x: r * theta.cos(), y: r * theta.sin())

impl StringInterner:
    # ✅ Factory with default capacity
    static fn with_capacity(capacity: i32) -> StringInterner:
        StringInterner(strings: {}, reverse: {}, next_id: 0)
        # Could add pre-allocation logic here in future

# Usage - clear intent:
val center = Point.origin()
val p = Point.from_polar(5.0, 0.785)
val interner = StringInterner.with_capacity(100)
```

**Why this pattern?**
- Direct construction is simplest: `Point(x: 3, y: 4)`
- Named factories are clearer than `.new()`: `Point.origin()` explains intent
- Return type automatically inferred to be the class
- No ambiguity about what constructor is being used

**Pattern Summary:**
- ✅ **Primary:** `ClassName(field: value)` - direct construction
- ✅ **Optional:** `static fn factory_name() -> ClassName` - named factories
- ❌ **Avoid:** `.new()` - not idiomatic in Simple, use named factories instead

**⚠️ CAUTION: Do NOT call `.new()` methods**

```simple
# ❌ WRONG - Don't do this:
val p = Point.new(3, 4)
val cache = Cache.new()
val interner = StringInterner.new()

# ✅ CORRECT - Do this instead:
val p = Point(x: 3, y: 4)                                              # Direct construction
val cache = Cache(items: {})                                           # Direct construction
val interner = StringInterner(strings: {}, reverse: {}, next_id: 0)   # Direct construction

# ✅ OR use named factories when helpful:
val center = Point.origin()
val cache = Cache.empty()
val interner = StringInterner.with_capacity(100)
```

Why `.new()` is wrong in Simple:
- Direct construction `ClassName(field: value)` is built-in - no method needed
- `.new()` adds unnecessary indirection
- It's not the Simple idiom (this is Java/Rust/Python-style, not Simple)
- Use named factories `ClassName.factory_name()` instead when you need custom initialization
- Return type is automatically inferred - just use `static fn factory_name()` with no explicit return type

**Methods (can be in class body OR impl block):**
```simple
# ✅ OPTION 1: Methods in class body (Simple-style)
class Point:
    x: i64
    y: i64

    fn get_x() -> i64:                  # Immutable method (self implicit)
        self.x

    me move(dx: i64, dy: i64):          # Mutable method ('me' keyword, self implicit)
        self.x = self.x + dx            # Can modify fields via self.field[key] = value
        self.y = self.y + dy

# ✅ OPTION 2: Methods in impl block (Rust-style, alternative)
impl Point:
    fn distance() -> f64:
        (self.x * self.x + self.y * self.y).sqrt()

# Key points:
# - Immutable methods: `fn method()` - can't modify self
# - Mutable methods: `me method()` - can modify self and fields
# - Static methods: `static fn factory()` - no self parameter
# - Both patterns work: in-class or in-impl
# - `self` is always implicit (don't write `self` in parameter list)
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

### Config Files and Data Format
- ✅ **USE SDN format** for all config/data files: `*.sdn`
- ❌ **NEVER use JSON** - use SDN table format instead
- ❌ **NEVER use TOML/YAML** - use SDN table format instead
- 📖 **SDN Parser**: Use `simple_sdn::parse_document()` from `simple_sdn` crate
- 📊 **Examples**: `doc/todo/todo_db.sdn`, `doc/feature/feature_db.sdn`

**Good Example (SDN table format):**
```sdn
todos |id, keyword, area, priority, description, file, line|
    0, TODO, doc, P1, "Add examples", README.md, 42
    1, FIXME, runtime, P0, "Fix leak", gc.rs, 123
```

**Bad Example (JSON - DO NOT USE):**
```json
{
  "todos": [
    {"id": "0", "keyword": "TODO", ...}
  ]
}
```

### Report
- **DO NOT ADD REPORT TO JJ** unless request it. See `doc/report/` for more details.

---

## Documentation

**Bug Reports:** `simple/bug_report.md`
**Improvement Requests:** `simple/improve_request.md`
**Job Reports:** `doc/report/` (completion reports, session summaries)
**Feature Specs:** `simple/std_lib/test/features/` - **Executable SSpec tests (see `/doc` skill)**
**Research:** `doc/research/` (investigation, design exploration)
**Guides:** `doc/guide/` (user-facing tutorials)

### Auto-Generated Documentation

Files automatically updated during development:

| File | Updated When | Command | Description |
|------|-------------|---------|-------------|
| `doc/TODO.md` | Manual | `simple todo-scan` | TODO/FIXME tracking from source code |
| `doc/feature/feature_db.sdn` | **Every test run** | `simple test` | Feature database (all features) |
| `doc/feature/feature.md` | **Every test run** | `simple test` | Feature index by category |
| `doc/feature/pending_feature.md` | **Every test run** | `simple test` | Incomplete features only (failed/in_progress/planned) |
| `doc/feature/category/*.md` | **Every test run** | `simple test` | Per-category feature lists |
| `doc/test/test_db.sdn` | **Every test run** | `simple test` | Test execution database (results + timing) |
| `doc/test/test_result.md` | **Every test run** | `simple test` | Test results (pass/fail + timing analysis) |
| `doc/build/build_db.sdn` | **Every build** | `simple build` | Build error/warning database |
| `doc/build/recent_build.md` | **Every build** | `simple build` | Build errors and warnings report (max 10 per file) |
| `doc/bug/bug_db.sdn` | Manual | `simple bug-add` | Bug tracking database (must link to test cases) |
| `doc/bug/bug_report.md` | Manual | `simple bug-gen` | Bug status report |

**Quick Access:**
- **What needs work?** → `doc/feature/pending_feature.md` (updated every test run)
- **Test results?** → `doc/test/test_result.md` (pass/fail + timing, updated every test run)
- **Build status?** → `doc/build/recent_build.md` (updated every build)
- **All TODOs?** → `doc/TODO.md` (run `simple todo-scan` to update)
- **All features?** → `doc/feature/feature.md` (updated every test run)
- **All bugs?** → `doc/bug/bug_report.md` (run `simple bug-gen` to update)

**Workflow:**
```bash
# Update TODO tracking (manual)
simple todo-scan
# Generates: doc/todo/todo_db.sdn + doc/TODO.md

# Build project (automatic error/warning tracking)
simple build
# Generates: doc/build/build_db.sdn + doc/build/recent_build.md

# Run tests (automatic doc generation)
simple test
# Generates: doc/feature/*.md + doc/test/test_result.md

# Add bug with required test case link
simple bug-add --id=bug_042 --reproducible-by=test_name
# Updates: doc/bug/bug_db.sdn

# Generate bug report
simple bug-gen
# Generates: doc/bug/bug_report.md
```

---

## Quick Commands

```bash
make check         # fmt + lint + test (before commit)
make check-full    # + coverage + duplication
make test-all      # Run ALL tests: Rust + doc-tests + Simple/SSpec (excludes skip/slow/ignore)
cargo test --workspace
./target/debug/simple script.spl
```

---

## Test Filtering and Test Types

### Test Types

| Type | Description | Markers | Auto-Ignored | Location |
|------|-------------|---------|--------------|----------|
| **Regular Tests** | Standard unit/integration tests | `it "..."`, `test "..."` | No | `*_spec.spl`, `*_test.spl` |
| **Slow Tests** | Long-running tests (>5s) | `slow_it "..."` | **Yes** (#[ignore]) | `*_spec.spl` |
| **Skipped Tests** | Not yet implemented features | Tag: `skip` | No | Any test file |
| **Rust Doc-Tests** | Executable documentation | Doc comments | Some | Rust source files |
| **Rust #[ignore] Tests** | Manually ignored Rust tests | `#[ignore]` | **Yes** | Rust test files |

### Listing Tests

```bash
# List all tests without running
./target/debug/simple test --list

# List tests with tags displayed
./target/debug/simple test --list --show-tags

# List only ignored tests (at Rust level)
./target/debug/simple test --list-ignored

# Count tests by type
./target/debug/simple test --list | wc -l              # Total tests
./target/debug/simple test --list-ignored | wc -l     # Ignored tests
```

### Running Specific Test Types

```bash
# Run all tests (excludes slow tests by default)
./target/debug/simple test

# Run only slow tests
./target/debug/simple test --only-slow

# Run only skipped tests (usually fail - they're unimplemented)
./target/debug/simple test --only-skipped

# Run tests matching a pattern
./target/debug/simple test pattern_here

# Run tests from specific file
./target/debug/simple test path/to/test_spec.spl

# Run with tag filtering (AND logic)
./target/debug/simple test --tag=integration --tag=database
```

### Doc-Tests (Rust)

```bash
# Run all doc-tests (workspace-wide)
cargo test --doc --workspace

# Run doc-tests for specific crate
cargo test --doc -p simple-driver
cargo test --doc -p arch_test
cargo test --doc -p simple-compiler

# Count total ignored doc-tests
cargo test --doc --workspace 2>&1 | grep " ... ignored$" | wc -l
```

### Test Markers Explained

**Simple Language Tests:**
- `it "description"` - Regular test (runs by default)
- `slow_it "description"` - Slow test (generates `#[ignore]`, run with `--only-slow`)
- Tags: `skip`, `integration`, `unit`, custom tags

**Rust Doc-Tests:**
- ` ```rust` - Executable doc-test
- ` ```ignore` - Ignored (not recommended - fix instead)
- ` ```no_run` - Compile-only (for runtime-dependent examples)
- ` ```text` - Not a code block (for examples)

### Test Filtering Flags

| Flag | Effect | Use Case |
|------|--------|----------|
| `--list` | List tests without running | See available tests |
| `--list-ignored` | List ignored tests | Find tests with #[ignore] |
| `--show-tags` | Show tags in output | Debug tag filtering |
| `--only-slow` | Run only slow_it() tests | Run long tests separately |
| `--only-skipped` | Run only skip-tagged tests | Check unimplemented features |
| `--tag=name` | Filter by tag | Run specific test categories |

### Examples

```bash
# Development workflow
./target/debug/simple test                    # Quick feedback (excludes slow)
./target/debug/simple test --only-slow        # Before commit (run slow tests)
cargo test --doc --workspace                  # Verify doc examples

# Investigation
./target/debug/simple test --list --show-tags           # See all tests with tags
./target/debug/simple test --only-skipped --list        # See unimplemented features
cargo test --doc -p simple-driver 2>&1 | grep ignored   # Check ignored doc-tests

# Targeted testing
./target/debug/simple test my_feature         # Run tests matching "my_feature"
./target/debug/simple test --tag=integration  # Run integration tests only
```

### Test Statistics

See auto-generated reports for current statistics:
- `doc/test/test_result.md` - Test results (updated every test run)
- `doc/test/grouped_test_db.sdn` - Grouped test status

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
