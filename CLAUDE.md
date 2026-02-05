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

**Empty statements (both `()` and `pass` are synonyms):**
```simple
# Unit value () - expression style (preferred)
match value:
    Some(x): process(x)
    None: ()                  # Do nothing, return unit value

# pass keyword - statement style (Python-familiar)
match value:
    Some(x): process(x)
    None: pass                # Do nothing, no-op statement

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
user?.name                    # Returns None if user is None
user?.profile?.settings       # Chain safe navigation
obj?.method()                 # Safe method call
user?.name ?? "Anonymous"     # Default if None
config["key"] ?? default      # Fallback value
```

**Existence check (`.?`) and no-paren methods:**
```simple
# .? checks if value is "present" (not nil AND not empty)
opt.?                         # true if Some, false if None
list.?                        # true if non-empty, false if empty
dict.?                        # true if non-empty, false if empty
str.?                         # true if non-empty string
num.?                         # always true (primitives exist)

# No-paren method calls (Ruby-like)
list.first                    # same as list.first()
list.last                     # same as list.last()
str.trim                      # same as str.trim()
str.upper                     # same as str.upper()

# Combine .? with no-paren for concise checks
list.first.?                  # true if list has first element
str.trim.?                    # true if trimmed string is non-empty

# Result type patterns (replaces is_ok/is_err)
result.ok.?                   # true if Ok (same as is_ok())
result.err.?                  # true if Err (same as is_err())

# Negation patterns
not opt.?                     # true if None (same as is_none())
not list.?                    # true if empty (same as is_empty())
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
- ❌ **NEVER write Python/Bash** - use Simple (`.spl`) for all scripts
- ✅ **Exception**: Bash (`.sh`) is ONLY allowed for bootstrapping scripts when Simple runtime doesn't exist:
  - GitHub Actions first-time builds (`script/build-bootstrap.sh`)
  - External installer scripts for users without Simple (`script/install.sh`)
  - These should be minimal wrappers that call Simple scripts when available

### Rust Files and SFFI (Simple FFI)
- ❌ **NEVER write `.rs` files manually** - all FFI is Simple-first
- ❌ **NEVER manually create Rust FFI implementations** - use `simple sffi-gen`
- ✅ **Write FFI specs in Simple** at `src/app/ffi_gen/specs/*.spl`
- ✅ **Generate Rust code**: `simple sffi-gen --gen-all` or `simple sffi-gen --gen-intern <spec.spl>`
- ✅ **Write SFFI wrappers in Simple** using the two-tier pattern:
  ```simple
  # Tier 1: Extern declaration (in src/app/io/mod.spl)
  extern fn rt_file_read_text(path: text) -> text

  # Tier 2: Simple-friendly wrapper
  fn file_read(path: text) -> text:
      rt_file_read_text(path)
  ```
- ✅ **Main SFFI module**: `src/app/io/mod.spl` (all extern fn declarations)
- ✅ **SFFI specs location**: `src/app/ffi_gen/specs/` (generates `build/rust/ffi_gen/src/`)
- 📖 **SFFI Skill**: See `/sffi` for complete patterns and type conversions

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
- ✅ **`?` is an operator only**:
  - `result?` - Try operator (unwrap or propagate error)
  - `T?` - Optional type
  - `expr?.field` - Optional chaining
  - `expr ?? default` - Null coalescing
  - `expr.?` - Existence check (is present/non-empty)
- ✅ **Prefer `.?` over `is_*` predicates**: `opt.?` instead of `opt.is_some()`
- 📖 **Design Decision**: See `doc/design/question_mark_design_decision.md`
- 📖 **Refactoring Guide**: See `doc/research/exists_check_refactoring.md`

### Caret Operator (`^`) and Math Blocks
- ✅ **Inside `m{}` blocks**: `^` is power operator (e.g., `m{ x^2 + y^2 }`)
- ❌ **Outside `m{}` blocks**: `^` produces lexer error
- ✅ **For exponentiation outside m{}**: Use `**` (e.g., `2 ** 3` for 2³)
- ✅ **For XOR**: Use `xor` keyword (e.g., `5 xor 3` for bitwise XOR)

### Math Language Features
- ✅ **`xor` keyword**: Bitwise XOR operator (e.g., `5 xor 3` → 6)
- ✅ **`@` operator**: Matrix multiplication (e.g., `A @ B`)
- ✅ **Dotted operators**: Element-wise broadcasting
  - `.+` broadcast add, `.-` broadcast sub
  - `.*` broadcast mul, `./` broadcast div
  - `.^` broadcast power
- ✅ **`m{}` math blocks**: Enable `^` as power operator
  ```simple
  # Normal code uses **
  val result = x ** 2

  # Math blocks use ^ for power
  val formula = m{ x^2 + 2*x*y + y^2 }
  ```

### Pipeline Operators
- ✅ **`|>` pipe forward**: Pass value to function (`x |> f` = `f(x)`)
- ✅ **`>>` compose**: Forward composition (`f >> g` = `λx. g(f(x))`)
- ✅ **`<<` compose back**: Backward composition (`f << g` = `λx. f(g(x))`)
- ✅ **`//` parallel**: Run operations in parallel
- ✅ **`~>` layer connect**: NN layer pipeline with **dimension checking**
  ```simple
  # Data processing pipeline
  val result = data |> normalize |> transform |> predict

  # Function composition
  val preprocess = normalize >> augment >> to_tensor

  # Neural network with compile-time dimension checking
  val model = Linear(784, 256) ~> ReLU() ~> Linear(256, 10)
  # Type: Layer<[batch, 784], [batch, 10]>

  # Compile-time error on dimension mismatch:
  val bad = Linear(784, 256) ~> Linear(128, 64)
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

### Build System (Simple - Recommended)

```bash
# Self-hosting build system written in Simple
simple build                    # Debug build
simple build --release          # Release build (40 MB)
simple build --bootstrap        # Bootstrap build (9.3 MB minimal)

simple build test               # Run all tests
simple build coverage           # Generate coverage reports
simple build lint               # Run clippy linter
simple build fmt                # Format code
simple build check              # All quality checks (lint + fmt + test)

simple build clean              # Clean build artifacts
simple build bootstrap          # 3-stage bootstrap pipeline
simple build bootstrap-rebuild  # Rebuild compiler from bootstrap binary
simple build package            # Create distribution packages
simple build watch              # Watch mode (auto-rebuild)
simple build metrics            # Show build metrics

# See full options
simple build --help
```

### Run a Simple Script

```bash
simple script.spl               # Run a Simple file
simple mcp server               # Start MCP server
simple test                     # Run all tests
```

### Development (requires Rust source)

> Note: These commands only work in development environment with `rust/` directory.
> Release distributions are pure Simple and don't need these commands.

```bash
# Rust subproject commands (development only)
simple build rust test                    # All Rust workspace tests
simple build rust test --doc              # Rust doc-tests only
simple build rust lint                    # Run clippy
simple build rust fmt                     # Run rustfmt
simple build rust clean                   # Clean Rust artifacts

# Run all tests (Rust + Simple/SSpec by default)
simple test                               # All tests (Rust + Simple/SSpec)
simple test --no-rust-tests               # Simple/SSpec tests only
simple test path/to/spec.spl             # Single test file
simple test --list                        # List tests without running

# Run lint on Simple code
simple lint src/app/fix/rules.spl

# Run fix with options
simple fix file.spl --dry-run        # Preview fixes
simple fix file.spl --fix-all         # Apply all fixes
simple fix file.spl --fix-interactive  # Prompt per fix
```

### Fixing Rust Warnings

When building shows warnings, fix them before committing:

```bash
# Check for warnings
simple build rust lint

# Common fixes:
# - "shared reference to mutable static" → Use OnceLock + AtomicUsize
# - "unused variable" → Prefix with _ or remove
# - "dead code" → Remove or add #[allow(dead_code)] with justification
```

### Binary Size Optimization

**Bootstrap Profile (Recommended for Releases):**

The bootstrap profile produces the smallest possible binary (9.3 MB, 76.8% reduction from standard release):

```bash
# Build with bootstrap profile
simple build --bootstrap

# Binary location
./rust/target/bootstrap/simple_runtime  # 9.3 MB

# Optional: Compress with UPX (requires: sudo apt-get install upx)
upx --best --lzma ./rust/target/bootstrap/simple_runtime  # → ~4.5 MB (88.8% total reduction)
```

**Build Profile Comparison:**

| Profile | Size | Use Case |
|---------|------|----------|
| Debug | 423 MB | Development (fast builds, debuggable) |
| Release | 40 MB | Standard optimized build |
| Bootstrap | 9.3 MB | Minimal size (distribution) |
| Bootstrap + UPX | ~4.5 MB | Maximum compression (distribution) |

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
| `simple_runtime` | `rust/target/{profile}/simple_runtime` | Rust | Core runtime (builds Simple code) |
| `simple` | `bin/simple` | Shell+Simple | Default CLI → `src/app/cli/main.spl` |
| `simple_runtime` | `bin/simple_runtime` | Shell | Runtime wrapper (discovers binary) |
| `simple` | `bin/bootstrap/simple` | Shell+Simple | Bootstrap CLI (minimal 9.3 MB) |
| `simple_runtime` | `bin/bootstrap/simple_runtime` | Rust | Bootstrap runtime (9.3 MB minimal) |

**All user-facing tools are now Simple apps** in `src/app/`. The Rust `simple_runtime` binary provides the runtime.

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
- Bootstrap can rebuild entire compiler with `simple build bootstrap-rebuild`

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
simple test --list

# List tests with tags displayed
simple test --list --show-tags

# List only ignored tests (at Rust level)
simple test --list-ignored

# Count tests by type
simple test --list | wc -l              # Total tests
simple test --list-ignored | wc -l     # Ignored tests
```

### Running Specific Test Types

```bash
# Run all tests (Rust + Simple/SSpec, excludes slow tests by default)
simple test

# Run only Simple/SSpec tests (skip Rust)
simple test --no-rust-tests

# Run only slow tests
simple test --only-slow

# Run only skipped tests (usually fail - they're unimplemented)
simple test --only-skipped

# Run tests matching a pattern
simple test pattern_here

# Run tests from specific file
simple test path/to/test_spec.spl

# Run with tag filtering (AND logic)
simple test --tag=integration --tag=database
```

### Doc-Tests (Rust)

```bash
# Run all doc-tests (workspace-wide)
simple build rust test --doc

# Run doc-tests for specific crate
simple build rust test --doc -p simple-driver
simple build rust test --doc -p arch_test
simple build rust test --doc -p simple-compiler

# Count total ignored doc-tests
simple build rust test --doc 2>&1 | grep " ... ignored$" | wc -l
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
simple test                    # All tests: Rust + Simple/SSpec (excludes slow)
simple test --no-rust-tests    # Quick feedback (Simple/SSpec only)
simple test --only-slow        # Before commit (run slow tests)
simple build rust test --doc   # Verify doc examples

# Investigation
simple test --list --show-tags           # See all tests with tags
simple test --only-skipped --list        # See unimplemented features
simple build rust test --doc -p simple-driver 2>&1 | grep ignored   # Check ignored doc-tests

# Targeted testing
simple test my_feature         # Run tests matching "my_feature"
simple test --tag=integration  # Run integration tests only
```

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
simple test --list-runs

# Cleanup stale runs (marks as crashed if running > 2 hours or process dead)
simple test --cleanup-runs

# Keep only 50 most recent runs
simple test --prune-runs=50

# List only running tests
simple test --list-runs --runs-status=running
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
simple --gen-lean module.spl --verify memory|types|effects|all
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
| Architecture | 100% Pure Simple |
| Self-Hosting Build | Complete (8 phases) |
| MCP Server | Complete (JSON-RPC 2.0) |
| Database Library | Complete (atomic ops) |
| Lexer/Parser/AST | Complete |
| HIR/MIR | Complete (50+ instructions) |
| Codegen | Hybrid (Cranelift + Interpreter) |
| RuntimeValue | Complete (9 modules, 50+ FFI) |
| BDD Framework | Sprint 1 Complete + 21 Feature Specs |
| Test Count | 631+ tests |

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
