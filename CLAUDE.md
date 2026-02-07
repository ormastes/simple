# Simple Language Compiler - Development Guide
Impl in simple unless it has big performance differences.

## 🎉 Recent Updates (2026-02-06)

**MAJOR: Rust source code completely removed - 100% Pure Simple achieved!**

- ✅ **BUG-042 FIXED:** `static assert` syntax now works (1-line parser fix)
- ✅ **BUG-043 FIXED:** `const fn` syntax now works (was already working)
- ✅ **Rust deleted:** 24.2GB freed (`rust/` + `build/rust/` removed)
- ✅ **Pure Simple parser:** 2,144 lines, fully self-hosting
- ✅ **No Rust toolchain needed:** Uses pre-built 27MB runtime
- 📖 **Report:** `doc/report/rust_removed_pure_simple_complete_2026-02-06.md`

**System is now 100% self-hosting in Simple language!**

### Pure Simple Build (v0.5.0+)

**Status:** All Rust build infrastructure removed. Build system operates entirely in Simple.

**Quick Build:**
```bash
bin/simple build --release    # Instant (<1s) - no compilation
```

**What Changed:**
- ✅ No Rust FFI generation required
- ✅ No cargo build required
- ✅ Uses pre-built 27MB runtime
- ✅ All source code in Simple (1,109+ .spl files)

**For Full Details:** See `doc/report/pure_simple_rebuild_success_2026-02-06.md`

---

## Skills Reference

For detailed guidance, invoke with `/skill-name`:

| Skill | Purpose |
|-------|---------|
| `versioning` | Jujutsu (jj) workflow - **NOT git!** |
| `test` | Test writing (Simple/SSpec BDD) |
| `sspec` | **SSpec BDD framework** - Testing → Doc generation workflow |
| `coding` | Coding standards, Simple language rules |
| `design` | Design patterns, type system, APIs |
| `architecture` | Compiler architecture, crate structure |
| `research` | Codebase exploration, documentation |
| `debug` | Debugging interpreter/codegen, tracing, GC logging |
| `stdlib` | Writing stdlib modules, variants, capabilities |
| `todo` | TODO/FIXME comment format |
| `doc` | Documentation writing: specs (SSpec), research, design, guides |
| `deeplearning` | **Deep learning**: Pipeline operators, dimension checking, NN layers |
| `sffi` | **SFFI wrappers**: Two-tier pattern (`extern fn` + wrapper), Simple FFI wrappers vs raw FFI |
| `database` | **Database library**: BugDB, TestDB, FeatureDB, atomic ops, query builder |
| `mcp` | **MCP server**: Model Context Protocol, resources, prompts, bug database integration |

Skills located in `.claude/skills/`.

**Full Syntax Reference:** `doc/guide/syntax_quick_reference.md` - Complete syntax guide with all features

**Writing SSpec Tests:**
- **Template:** `.claude/templates/sspec_template.spl` - Copy this for new specs
- **Complete Example:** `doc/guide/sspec_complete_example.md` - Full workflow
- **Quick Start:** `/sspec` skill or `cat .claude/skills/sspec.md`

---

## Key Features

- **Self-Hosting Build System**: Complete build system written in Simple (100% complete)
  - 8 phases: Foundation, Testing, Coverage, Quality, Bootstrap, Package, Migration, Advanced
  - 4,440 lines of implementation, 2,370 lines of tests (290+ SSpec tests)
  - Commands: `build`, `test`, `coverage`, `lint`, `fmt`, `check`, `bootstrap`, `package`
  - Replaces Makefile with type-safe Simple code
  - See: `doc/build/getting_started.md`, `src/app/build/`
- **Unified Database Library**: Production-ready database infrastructure (100% complete)
  - Core: `StringInterner`, `SdnTable`, `SdnRow`, `SdnDatabase` (O(1) operations)
  - Atomic operations with file-based locking (2-hour stale lock detection)
  - Query builder with fluent API (filters, sorting, limits)
  - Domain databases: `BugDatabase`, `TestDatabase`, `FeatureDatabase`
  - 27/27 tests passing + 80+ integration tests
  - SDN file format for human-readable storage
  - See: `src/lib/database/`, `test/lib/database_spec.spl`
- **MCP Server**: Model Context Protocol integration (ready for production)
  - Resources: File, symbol, type, documentation, directory tree access
  - Prompts: Refactoring, code generation, documentation, analysis templates
  - Bug Database integration: JSON API for bug tracking (`bugdb://` URIs)
  - Query API integration for compiler introspection
  - See: `src/app/mcp/`, `doc/report/mcp_database_integration_2026-02-05.md`
- **File Extensions**:
  - `.spl` - Simple source files (modules, libraries, AND executable scripts with `#!/usr/bin/env simple`)
  - `.sspec` - SSpec test/specification files
  - `.sh` - Bash scripts (ONLY for bootstrapping when Simple runtime doesn't exist yet)
  - **Note**: Use `.spl` for everything in Simple. Add `#!/usr/bin/env simple` + `chmod +x` for executable scripts. Don't use `.ssh` (conflicts with SSH)
- **LLM-Friendly**: IR export, context packs, lint framework (75% complete)
  - **New Lints**: `print_in_test_spec`, `todo_format`
  - **EasyFix Rules** (9 auto-fix rules): See `/coding` skill and `src/app/fix/rules.spl`
- **Pattern Matching Safety**: Exhaustiveness checking (5/5 complete)
- **Scala-Style Syntax**: `val`/`var` variables, implicit `self` in methods
- Memory model: Reference capabilities (`mut T`, `iso T`, `T`)
- Formatter/linter: `src/app/`
- AOP & Unified Predicates: 19/51 features, 611 tests

---

## Syntax Quick Reference

**Variables:**
<!--sdoctest:skip-next-->
```simple
name = "Alice"    # Immutable (preferred)
other_name = "Bob".   # Immutable same as 'name = "Bob"'
var count = 0         # Mutable
```

**Implicit val/var (type inference, future/experimental):**
<!--sdoctest:skip-next-->
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
<!--sdoctest:skip-next-->
```simple
fn square(x):
    x * x                     # Last expression is returned (preferred)

fn explicit_return(x):
    return x * x              # Use only when needed for clarity
```

**Empty statements (both `()` and `pass` are synonyms):**
```simple
# Unit value () - expression style (preferred)
match value:
    Some(x): process(x)
    nil: ()                   # Do nothing, return unit value

# pass keyword - statement style (Python-familiar)
match value:
    Some(x): process(x)
    nil: pass                 # Do nothing, no-op statement

# Both compile to identical code - use whichever is clearer
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
user?.name                    # Returns nil if user is nil
user?.profile?.settings       # Chain safe navigation
obj?.method()                 # Safe method call
user?.name ?? "Anonymous"     # Default if nil
config["key"] ?? default      # Fallback value
```

**Existence check (`.?`) and no-paren methods:**
<!--sdoctest:skip-next-->
```sdoctest:skip
# .? checks if value is "present" (not nil AND not empty)
# SKIPPED: .? operator may not be fully implemented
>>> opt = Some(42)
>>> opt.?
true
>>> list = [1, 2, 3]
>>> list.?
true
>>> empty_list = []
>>> empty_list.?
false
```

**Refactoring patterns (prefer `.?` style):**
| Verbose | Concise | Notes |
|---------|---------|-------|
| `opt.is_some()` | `opt.?` | Direct existence check |
| `opt.is_none()` | `not opt.?` | Negated existence |
| `result.is_ok()` | `result.ok.?` | `ok` returns Option |
| `result.is_err()` | `result.err.?` | `err` returns Option |
| `list.is_empty()` | `not list.?` | Empty = not present |
| `list.first().is_some()` | `list.first.?` | No-paren + existence |

**Strings:**
```simple
print "Hello, {name}!"        # Interpolation is default (no f"" needed)
print "Result: {x + y}"       # Expressions in braces
print r"regex: \d+{3}"        # Raw string (no interpolation, no escapes)
```

**Format String Templates (Future):**
<!--sdoctest:skip-next-->
```simple
# Template with auto-detected const keys
template = "Welcome {user} to {city}"

# Instantiate with dict - keys auto-validated at compile time
greeting = template.with {"user": username, "city": current_city}

# Compile errors for wrong keys (no type annotation needed):
bad = template.with {"usr": x}   # ERROR: "usr" not in ["user", "city"]
missing = template.with {"user": x}  # ERROR: Missing key "city"
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
p = Point(x: 3, y: 4)
interner = StringInterner(strings: {}, reverse: {}, next_id: 0)
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
center = Point.origin()
p = Point.from_polar(5.0, 0.785)
interner = StringInterner.with_capacity(100)
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
# ❌ WRONG:  Point.new(3, 4), Cache.new(), StringInterner.new()
# ✅ CORRECT: Point(x: 3, y: 4), Cache(items: {}), Point.origin()
```

Why `.new()` is wrong in Simple:
- Direct construction `ClassName(field: value)` is built-in - no method needed
- `.new()` adds unnecessary indirection - not the Simple idiom
- Use named factories `ClassName.factory_name()` for custom initialization

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

### Scripts and Executable Files

- ✅ **USE Simple (.spl)** for ALL scripts and automation
- ❌ **NEVER use Python (.py)** - migrate to Simple
- ❌ **NEVER use Bash (.sh)** - except for 3 bootstrap scripts below

**Bootstrap Exceptions (ONLY these 3 files allowed as .sh):**
1. `script/build-bootstrap.sh` - GitHub Actions first build
2. `script/build-full.sh` - Release package builder
3. `script/install.sh` - End-user installer (no Simple runtime)

These scripts run BEFORE Simple runtime exists, so they must be Bash.

**All other scripts must be Simple:**
- Build utilities: `src/app/build/*.spl`
- Verification: `src/app/verify/*.spl`
- Code generation: `src/app/doc/*.spl`
- Testing: `src/app/test/*.spl`
- Version control wrappers: `script/jj-wrappers/*.sh` (kept for compatibility)

**Executable Scripts:**
Use `#!/usr/bin/env simple` shebang and `chmod +x`:
```simple
#!/usr/bin/env simple
use app.io

fn main():
    # Script logic here
```

### Rust Files - REMOVED ✅

**As of 2026-02-06: Rust source code completely removed (24.2GB freed)**

- ✅ **No Rust source files** - `rust/` directory deleted
- ✅ **Pure Simple parser** - 100% self-hosting
- ✅ **Pre-built runtime** - `release/simple-0.4.0-beta/bin/simple_runtime` (27MB)
- ✅ **No Rust toolchain needed** - rustc/cargo not required

### SFFI (Simple FFI) - Pure Simple Approach

- ✅ All FFI uses the **two-tier pattern** (`extern fn` + wrapper) - see [SFFI Wrappers](#sffi-wrappers-simple-ffi---simple-first-approach) section for details
- ✅ **Main SFFI module**: `src/app/io/mod.spl`
- 📖 **SFFI Skill**: See `/sffi` for complete patterns

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

### Pattern Binding Syntax (`if val` / `if var`)
- ✅ **USE `if val`**: `if val Some(x) = expr:` (immutable pattern binding)
- ✅ **USE `if var`**: `if var Some(x) = expr:` (mutable pattern binding)
- ❌ **DEPRECATED `if let`**: Emits warning, use `if val` instead
- 🔧 **EasyFix**: Rule `L:deprecated_if_let` auto-replaces `if let` → `if val`
- Also applies to `while let` → `while val` and `elif let` → `elif val`

### Question Mark (`?`) Usage
- ❌ **NEVER use `?` in method/function/variable names** - unlike Ruby
- ✅ **`?` is an operator only**: `result?` (try), `T?` (optional type), `?.` (chaining), `??` (coalescing), `.?` (existence)
- ✅ **Prefer `.?` over `is_*` predicates** - see Syntax Quick Reference above for full `.?` examples
- 📖 **Design Decision**: See `doc/design/question_mark_design_decision.md`

### Math Language Features and Caret Operator (`^`)
- ✅ **`m{}` math blocks**: `^` is power operator inside (e.g., `m{ x^2 + y^2 }`)
- ❌ **Outside `m{}` blocks**: `^` produces lexer error - use `**` instead (e.g., `2 ** 3` for 2³)
- ✅ **`xor` keyword**: Bitwise XOR operator (e.g., `5 xor 3` → 6)
- ✅ **`@` operator**: Matrix multiplication (e.g., `A @ B`)
- ✅ **Dotted operators**: Element-wise broadcasting
  - `.+` broadcast add, `.-` broadcast sub
  - `.*` broadcast mul, `./` broadcast div
  - `.^` broadcast power
  ```simple
  # Normal code uses **
  result = x ** 2

  # Math blocks use ^ for power
  formula = m{ x^2 + 2*x*y + y^2 }
  ```

### Pipeline Operators
- ✅ **`|>` pipe forward**: Pass value to function (`x |> f` = `f(x)`)
- ✅ **`>>` compose**: Forward composition (`f >> g` = `λx. g(f(x))`)
- ✅ **`<<` compose back**: Backward composition (`f << g` = `λx. f(g(x))`)
- ✅ **`//` parallel**: Run operations in parallel
- ✅ **`~>` layer connect**: NN layer pipeline with **dimension checking**
  ```simple
  # Data processing pipeline
  result = data |> normalize |> transform |> predict

  # Function composition
  preprocess = normalize >> augment >> to_tensor

  # Neural network with compile-time dimension checking
  model = Linear(784, 256) ~> ReLU() ~> Linear(256, 10)
  # Type: Layer<[batch, 784], [batch, 10]>

  # Compile-time error on dimension mismatch:
  bad = Linear(784, 256) ~> Linear(128, 64)
  # ERROR[E0502]: output [batch, 256] != input [batch, 128]
  ```
- 📖 **Design**: See `doc/design/pipeline_operators_design.md`
- 📖 **Error Guide**: See `doc/guide/dimension_errors_guide.md`

### TODO Comments
- ❌ **NEVER remove TODO markers** unless the feature is fully implemented and working
- ✅ Can add documentation/implementation notes to existing TODOs
- ✅ Only delete TODO comment when code implementing that feature is complete
- 📊 **Status**: See `doc/report/todo_status_2026-01-16.md`

### Config Files and Data Format
- ✅ **USE SDN format** for all Simple config/data files: `*.sdn`
  - **Package manifests**: `simple.sdn` (preferred) or `simple.toml` (legacy support)
  - **Data/tracking files**: `*.sdn` only
  - **Test configuration**: `simple.test.sdn`
- ❌ **NEVER use JSON** for Simple configs - use SDN format instead
- ❌ **NEVER use YAML** for Simple configs - use SDN format instead
- ℹ️ **Rust tooling**: `Cargo.toml` is acceptable (Rust standard, not Simple config)
- 📖 **SDN Parser**: Use `simple_sdn::parse()` from `simple_sdn` crate
- 📊 **Examples**: `doc/todo/todo_db.sdn`, `doc/feature/feature_db.sdn`, `simple.sdn`

**Good Example (SDN manifest):**
```sdn
package:
  name: my-project
  version: 1.0.0

dependencies:
  http: 2.0
  json:
    version: 1.5
    features: [serde]
```

**Good Example (SDN table format):**
```sdn
todos |id, keyword, area, priority, description, file, line|
    0, TODO, doc, P1, "Add examples", README.md, 42
    1, FIXME, runtime, P0, "Fix leak", gc.rs, 123
```

**Legacy Support (will be phased out):**
```toml
# simple.toml - Legacy format (still supported, but prefer .sdn)
[package]
name = "my-project"
version = "1.0.0"
```

**Migration Status:**
- ✅ SDN parser implemented in `rust/sdn/`
- ✅ Package manifest supports both `.sdn` (preferred) and `.toml` (legacy)
- ✅ Data tracking files use SDN exclusively
- 🔄 Existing `.toml` manifests will be migrated to `.sdn` over time
- 📝 Use `simple init` to create new projects with `.sdn` manifests

### Report
- **DO NOT ADD REPORT TO JJ** unless request it. See `doc/report/` for more details.

---

## Project Directory Structure

### Standardized Directories

All directories follow consistent naming conventions:

| Directory | Purpose | Convention | Gitignored |
|-----------|---------|------------|------------|
| `examples/` | Example scripts and demos | **Plural** | No |
| `script/` | Build and utility scripts | **Singular** | No |
| `doc/` | Documentation root | **Singular** | No |
| `doc/architecture/` | Architecture docs | **Full name** (not `arch/`) | No |
| `doc/feature/` | Auto-generated feature docs | **Singular** (category) | No |
| `doc/spec/tooling/` | Tool specifications | **Plural** (collection) | No |
| `test/` | Test files | **Singular** | No |
| `src/` | Source code | **Singular** | No |
| `build/` | Build artifacts | **Singular** | Yes (`/build/`) |
| `.coverage/` | Runtime coverage data | **Hidden** (dotfile) | Yes (`.coverage/`) |

### Coverage Output Locations

Two types of coverage with separate locations:

**Runtime Coverage (Simple interpreter decision/condition/path coverage):**
- **Location**: `.coverage/coverage.sdn`
- **Tool**: Simple runtime with `SIMPLE_COVERAGE=1`
- **Format**: SDN (Simple Data Notation)
- **Config**: `rust/lib/std/src/tooling/coverage.spl` line 100

### Directory Naming Rules

✅ **DO:**
- Use **plural** for collections: `examples/`, `tooling/`
- Use **singular** for categories: `feature/`, `script/`, `doc/`
- Use **full names**: `architecture/` not `arch/`
- Keep build artifacts in `build/`: `build/coverage/`, `build/release/`
- Use **dotfiles** for runtime data: `.coverage/`

❌ **DON'T:**
- Create duplicate directories (e.g., both `example/` and `examples/`)
- Use abbreviations (e.g., `arch/` instead of `architecture/`)
- Scatter coverage outputs (use `.coverage/` for runtime, `build/coverage/` for build)
- Put build artifacts at root level

### Deleted Directories (Consolidated)

The following directories were removed during refactoring (2026-02-05):
- `example/` → consolidated into `examples/`
- `scripts/` → consolidated into `script/`
- `coverage/` and `coverage_new/` → replaced by `build/coverage/`
- `doc/arch/` → consolidated into `doc/architecture/`
- `doc/features/` → consolidated into `doc/feature/`
- `doc/spec/tools/` → consolidated into `doc/spec/tooling/`
- `src/src/` → deleted (nested artifact)
- Empty test directories: `test/basic/`, `test/benchmark/`, `test/unit/`

---

## Documentation

**Bug Reports:** `doc/bug_report.md`
**Improvement Requests:** `doc/improve_request.md`
**Job Reports:** `doc/report/` (completion reports, session summaries)
**Feature Specs:** `src/std/test/features/` - **Executable SSpec tests (see `/doc` skill)**
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
bin/simple todo-scan
# Generates: doc/todo/todo_db.sdn + doc/TODO.md

# Build project (automatic error/warning tracking)
bin/simple build
# Generates: doc/build/build_db.sdn + doc/build/recent_build.md

# Run tests (automatic doc generation)
bin/simple test
# Generates: doc/feature/*.md + doc/test/test_result.md

# Add bug with required test case link
bin/simple bug-add --id=bug_042 --reproducible-by=test_name
# Updates: doc/bug/bug_db.sdn

# Generate bug report
bin/simple bug-gen
# Generates: doc/bug/bug_report.md
```

---

## Quick Commands

### Build System (Simple - Recommended)

```bash
# Self-hosting build system written in Simple
bin/simple build                    # Debug build
bin/simple build --release          # Release build (40 MB)
bin/simple build --bootstrap        # Bootstrap build (9.3 MB minimal)

bin/simple build test               # Run all tests
bin/simple build coverage           # Generate coverage reports
bin/simple build lint               # Run clippy linter
bin/simple build fmt                # Format code
bin/simple build check              # All quality checks (lint + fmt + test)

bin/simple build clean              # Clean build artifacts
bin/simple build bootstrap          # 3-stage bootstrap pipeline
bin/simple build bootstrap-rebuild  # Rebuild compiler from bootstrap binary
bin/simple build package            # Create distribution packages
bin/simple build watch              # Watch mode (auto-rebuild)
bin/simple build metrics            # Show build metrics

# See full options
bin/simple build --help
```

### Run a Simple Script

```bash
bin/simple script.spl               # Run a Simple file
bin/simple mcp server               # Start MCP server
```

### Development (Pure Simple - No Rust)

> **As of 2026-02-06:** All Rust source removed. System is 100% pure Simple.
> All development commands work without Rust toolchain.

```bash
# Run all tests (Pure Simple/SSpec)
bin/simple test                               # All tests
bin/simple test path/to/spec.spl             # Single test file
bin/simple test --list                        # List tests without running

# Run lint on Simple code
bin/simple lint src/app/fix/rules.spl

# Run fix with options
bin/simple fix file.spl --dry-run        # Preview fixes
bin/simple fix file.spl --fix-all         # Apply all fixes
bin/simple fix file.spl --fix-interactive  # Prompt per fix
```

### Binary Size Optimization

**Pre-Built Runtime (Current Approach):**

The runtime is pre-built and included in the release (no Rust compilation needed):

```bash
# Pre-built runtime location
release/simple-0.4.0-beta/bin/simple_runtime  # 27 MB

# Symlink for easy access
bin/simple_runtime -> ../release/simple-0.4.0-beta/bin/simple_runtime
```

**Runtime Profile:**

| Profile | Size | Location | Source |
|---------|------|----------|--------|
| Pre-built Runtime | 27 MB | `release/simple-0.4.0-beta/bin/` | Included in distribution |
| Simple Source | 4.2 MB | `src/` | Pure Simple code |
| **Total System** | **31.2 MB** | - | Runtime + Source |

**UPX Compression Library:**

Simple programs can compress executables using the `compress.upx` module:

```simple
import compress.upx

# Compress binary
upx.compress("myapp", level: "best")

# Check compression
if upx.is_compressed("myapp"):
    val ratio = upx.get_ratio("myapp")
    print "Compressed {ratio}x"
```

**Documentation:**
- Implementation: `doc/report/upx_library_implementation_2026-01-31.md`
- Completion: `doc/report/binary_size_reduction_completion_2026-01-31.md`

### Executable Architecture

| Binary | Location | Language | Purpose |
|--------|----------|----------|---------|
| `simple` | `bin/simple` | Shell+Simple | Default CLI → `src/app/cli/main.spl` |
| `simple_runtime` | `bin/simple_runtime` | Shell | Runtime wrapper (discovers binary) |
| `simple_runtime` | `bin/bootstrap/simple_runtime` | Pre-built | Bootstrap runtime (27 MB) |

**All user-facing tools are Simple apps** in `src/app/`. The pre-built `simple_runtime` binary provides the runtime.

### Setting up PATH

Add both `bin/` and `bin/bootstrap/` to your PATH:

```bash
# Add to ~/.bashrc or ~/.zshrc
export PATH="/home/ormastes/dev/pub/simple/bin:/home/ormastes/dev/pub/simple/bin/bootstrap:$PATH"

# Or use relative path if working in repository
export PATH="$(pwd)/bin:$(pwd)/bin/bootstrap:$PATH"
```

This allows:
- `simple` - Uses development build first, falls back to bootstrap
- `bin/bootstrap/simple` - Always uses minimal bootstrap binary
- Bootstrap can rebuild entire compiler with `bin/simple build bootstrap-rebuild`

---

## Test Filtering and Test Types

### Test Types

| Type | Description | Markers | Auto-Ignored | Location |
|------|-------------|---------|--------------|----------|
| **Regular Tests** | Standard unit/integration tests | `it "..."`, `test "..."` | No | `*_spec.spl`, `*_test.spl` |
| **Slow Tests** | Long-running tests (>5s) | `slow_it "..."` | **Yes** (#[ignore]) | `*_spec.spl` |
| **Skipped Tests** | Not yet implemented features | Tag: `skip` | No | Any test file |

### Listing Tests

```bash
# List all tests without running
bin/simple test --list

# List tests with tags displayed
bin/simple test --list --show-tags

# List only ignored tests
bin/simple test --list-ignored

# Count tests by type
bin/simple test --list | wc -l              # Total tests
bin/simple test --list-ignored | wc -l     # Ignored tests
```

### Running Specific Test Types

```bash
# Run all tests (excludes slow tests by default)
bin/simple test

# Run only slow tests
bin/simple test --only-slow

# Run only skipped tests (usually fail - they're unimplemented)
bin/simple test --only-skipped

# Run tests matching a pattern
bin/simple test pattern_here

# Run tests from specific file
bin/simple test path/to/test_spec.spl

# Run with tag filtering (AND logic)
bin/simple test --tag=integration --tag=database
```

### Test Markers Explained

**Simple Language Tests:**
- `it "description"` - Regular test (runs by default)
- `slow_it "description"` - Slow test (generates `#[ignore]`, run with `--only-slow`)
- Tags: `skip`, `integration`, `unit`, custom tags

### Test Filtering Flags

| Flag | Effect | Use Case |
|------|--------|----------|
| `--list` | List tests without running | See available tests |
| `--list-ignored` | List ignored tests | Find tests with #[ignore] |
| `--show-tags` | Show tags in output | Debug tag filtering |
| `--only-slow` | Run only slow_it() tests | Run long tests separately |
| `--only-skipped` | Run only skip-tagged tests | Check unimplemented features |
| `--tag=name` | Filter by tag | Run specific test categories |

### Test Statistics

See auto-generated reports for current statistics:
- `doc/test/test_result.md` - Test results (updated every test run)
- `doc/test/grouped_test_db.sdn` - Grouped test status

### Test Run Tracking

Test runs are automatically tracked in `doc/test/test_db.sdn` (in the `test_runs` table).

**Run Management Commands:**

| Flag | Effect | Use Case |
|------|--------|----------|
| `--list-runs` | List all test runs | See run history |
| `--cleanup-runs` | Mark stale runs as crashed | Clean up dead processes |
| `--prune-runs=N` | Delete old runs, keep N most recent | Limit run history size |
| `--runs-status=STATUS` | Filter runs by status | Filter by running/completed/crashed |

**Examples:**

```bash
# List all test runs
bin/simple test --list-runs

# Cleanup stale runs (marks as crashed if running > 2 hours or process dead)
bin/simple test --cleanup-runs

# Keep only 50 most recent runs
bin/simple test --prune-runs=50

# List only running tests
bin/simple test --list-runs --runs-status=running
```

**Run Record Fields:**
- `run_id` - Unique ID (timestamp-based)
- `start_time`, `end_time` - ISO 8601 timestamps
- `pid`, `hostname` - Process ID and machine name
- `status` - `running`, `completed`, `crashed`, `timed_out`, `interrupted`
- `test_count`, `passed`, `failed`, `crashed`, `timed_out` - Test counts

---

## Lean 4 Verification

```bash
bin/simple --gen-lean module.spl --verify memory|types|effects|all
```

Projects in `verification/`: borrow checker, GC safety, effects, SC-DRF.

---

## SFFI Wrappers (Simple FFI - Simple-First Approach)

**All SFFI wrappers are written in Simple using the two-tier pattern.**

**Terminology:**
- **SFFI (Simple FFI)**: FFI wrappers written in Simple using the two-tier pattern
- **Raw FFI**: Direct `extern fn` declarations or Rust FFI code
- **SFFI wrapper**: The Simple wrapper function that calls `extern fn`
- **SFFI-gen**: Tool to generate Rust FFI code from Simple specs

### Two-Tier Pattern

```simple
# Tier 1: Extern declaration (raw FFI binding)
extern fn rt_file_read_text(path: text) -> text

# Tier 2: Simple-friendly wrapper (idiomatic API)
fn file_read(path: text) -> text:
    rt_file_read_text(path)
```

**Why two tiers?**
- `extern fn` - Raw binding to runtime, prefixed with `rt_`
- Wrapper `fn` - Clean API for Simple users, handles type conversions

### Main SFFI Module

All SFFI declarations live in `src/app/io/mod.spl`:

| Category | Prefix | Examples |
|----------|--------|----------|
| File | `rt_file_` | read, write, exists, copy, delete |
| Directory | `rt_dir_` | create, list, walk, remove |
| Environment | `rt_env_` | cwd, home, get, set |
| Process | `rt_process_` | run, run_timeout, run_with_limits |
| Time | `rt_time_`, `rt_timestamp_` | now, year, month, day |
| System | `rt_getpid`, `rt_hostname` | pid, hostname, cpu_count |
| CLI | `rt_cli_` | run_file, run_tests, run_lint |

### Adding New SFFI Functions

1. **Add extern declaration** in `src/app/io/mod.spl`:
   ```simple
   extern fn rt_my_function(arg1: text, arg2: i64) -> bool
   ```

2. **Add wrapper function**:
   ```simple
   fn my_function(arg1: text, arg2: i64) -> bool:
       rt_my_function(arg1, arg2)
   ```

3. **Group with section comment**:
   ```simple
   # --- My category ---
   extern fn rt_my_function(...)
   fn my_function(...)
   ```

### Type Conversions

| Simple Type | Rust Type | Notes |
|-------------|-----------|-------|
| `text` | `String` | Automatic |
| `i64`, `i32` | `i64`, `i32` | Direct |
| `bool` | `bool` | Direct |
| `[text]` | `Vec<String>` | Array of strings |
| `(text, text, i64)` | Tuple | Multiple returns |
| `[text]?` | `Option<Vec<String>>` | Optional |

### SFFI Error Handling Patterns

```simple
# Pattern 1: Boolean return
fn file_write(path: text, content: text) -> bool:
    rt_file_write_text(path, content)

# Pattern 2: Tuple with error info
fn process_run(cmd: text, args: [text]) -> (text, text, i64):
    rt_process_run(cmd, args)  # (stdout, stderr, exit_code)

# Pattern 3: Empty string for failure
fn env_get(key: text) -> text:
    rt_env_get(key)  # "" if not set
```

### See Also

- `/sffi` skill - Complete SFFI patterns and examples
- `src/app/io/mod.spl` - Main SFFI wrapper module
- `doc/guide/sffi_gen_guide.md` - SFFI generation guide (formerly ffi_gen_guide.md)

---

## Current Status (v0.4.0)

| Component | Status |
|-----------|--------|
| Architecture | 🎉 **100% Pure Simple - Zero Rust Source** |
| Self-Hosting Build | Complete (8 phases) |
| MCP Server | Complete (JSON-RPC 2.0) |
| Database Library | Complete (atomic ops) |
| Lexer/Parser/AST | **Pure Simple** (2,144 lines) |
| HIR/MIR | Complete (50+ instructions) |
| Codegen | Hybrid (Cranelift + Interpreter) |
| RuntimeValue | Pre-built binary (27MB) |
| BDD Framework | Sprint 1 Complete + 21 Feature Specs |
| Test Count | 631+ tests |
| Disk Usage | **24.2GB freed** (removed Rust) |

---

## Roadmap (v0.5.0)

**Priority:**
- Grammar refactoring and syntax improvements
- DL module path resolution fix
- Documentation consistency

**High:** LLM Features, Test Framework, LSP completion
**Medium:** TUI Framework, Package Registry
**Blocked:** Generator JIT codegen

See `doc/VERSION.md` for full version history.
