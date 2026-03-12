# Lint Guide

The Simple compiler includes a multi-layer lint system for detecting code quality issues, performance anti-patterns, and stub/dummy implementations.

---

## Quick Start

```bash
# Run linter on a file
bin/simple lint file.spl

# Run lint via build system
bin/simple build lint

# Run all quality checks (includes lint)
bin/simple build check
```

---

## Lint Layers

The lint system operates at three layers:

### 1. AST-Based Semantic Lints (`src/compiler/35.semantics/lint/`)

Deep analysis using the arena-based AST. Runs during compilation.

| Code | Category | Severity | Description |
|------|----------|----------|-------------|
| COLL001 | Collection | CRITICAL | Array concat in loop `arr = arr + [x]` — use `.push()` |
| COLL002 | Collection | HIGH | `.contains()` on array in loop — use Dict/Set |
| COLL003 | Collection | HIGH | `.remove(0)` queue drain in loop |
| COLL004 | Collection | MEDIUM | Loop-invariant method call — hoist before loop |
| COLL005 | Collection | MEDIUM | Chained `.filter().filter()` — combine predicates |
| COLL006 | Collection | CRITICAL | String concat in loop — use StringBuilder |
| COLL007 | Collection | HIGH | Array rebuild to pop last — use `.pop()` |
| COLL008 | Collection | MEDIUM | Unbounded global `.push()` with no reset |
| DTYP001 | Type Safety | WARNING | Positional args sharing type — use named args |
| STUB001 | Stub Impl | WARNING | Function with params returns trivial value, params unused |
| STUB002 | Stub Impl | INFO | Zero-param function returns default value (possible stub) |

### 2. Text-Scanning EasyFix Rules (`src/compiler/90.tools/fix/`)

Line-by-line text analysis with machine-applicable fixes.

| Rule ID | Confidence | Description |
|---------|------------|-------------|
| L:print_in_test_spec | Likely | Replace `print()` with `expect()` in test specs |
| L:unnamed_duplicate_typed_args | Uncertain | Add names for duplicate-typed params |
| L:resource_leak | Uncertain | Wrap resource in `with` block |
| L:sspec_missing_docstrings | Safe | Add template docstring to describe/context |
| L:sspec_manual_assertions | Likely | Replace manual `if/fail` with `expect()` |
| L:non_exhaustive_match | Safe | Add missing match arms with `todo()` |
| E:typo_suggestion | Likely | Fix misspelled identifiers |
| E:parser_contextual_keyword | Likely | Fix contextual keyword syntax |
| E:type_mismatch_coercion | Uncertain | Insert type coercion |
| L:deprecated_if_let | Likely | Replace `if let` with `if val` |
| L:struct_construction_parens | Safe | Fix struct construction syntax |
| L:stub_impl | Likely | Function with params returns trivial literal |
| L:unknown_decorator | Likely | Unknown `@decorator` not in whitelist |
| L:unknown_attribute | Likely | Unknown `#[attribute]` not in whitelist |
| L:export_outside_init | Certain | `export` statement outside `__init__.spl` |
| L:init_boundary_violation | Uncertain | Import bypasses `__init__.spl` boundary |
| L:bypass_with_code_files | Uncertain | `#[bypass]` in `__init__.spl` with sibling code |
| L:bare_bool | Uncertain | Bare `bool` parameter — suggest enum |
| L:sspec_no_print_based_tests | Certain | Print-based BDD framework in `_spec.spl` |
| L:sspec_minimal_docstrings | Likely | Test file has too few docstrings |

### 3. Semantic Linter Tool (`src/compiler/90.tools/lint/main.spl`)

Combined pattern-based + EasyFix pipeline with severity control.

| Category | Codes | Description |
|----------|-------|-------------|
| Safety (S) | S001-S003 | Memory safety, null checks, unsafe blocks |
| Correctness (C) | C001-C003 | Unreachable code, non-exhaustive match, type mismatch |
| Warning (W) | W001-W003 | Unused variables/imports, dead code |
| Style (ST) | ST001-ST003 | Naming conventions (snake_case, PascalCase, UPPER_SNAKE) |
| Concurrency (CC) | CC001-CC002 | Shared mutable state, thread safety |
| Database (D) | D001 | Direct database file writes |
| TODO (T) | T001-T004 | TODO/FIXME format compliance |
| Import (I) | I001-I003 | Unfold declarations, missing __init__.spl |
| Stub (STUB) | STUB001-STUB002 | Trivial/dummy implementations |
| Arguments (ARG) | ARG001-ARG002 | Too many function parameters |

---

## Argument Count Lint (ARG001/ARG002)

Detects functions with too many parameters, which hurts readability and is often a sign the function should be refactored.

### ARG001: Too Many Parameters (WARNING)

Fires when a function has more than 7 parameters (excluding `self`).

```simple
# WARNED — 8 parameters
fn create_user(name: text, email: text, age: i64, role: text,
               dept: text, manager: text, office: text, phone: text):
    ...
```

### ARG002: Excessive Parameters (ERROR)

Fires when a function has more than 12 parameters.

### What is NOT Flagged

```simple
# Constructors (need all struct fields)
fn new(name: text, email: text, age: i64, role: text,
       dept: text, manager: text, office: text, phone: text) -> User:
    ...

# FFI wrappers (_ffi_ or _raw_ prefix)
fn _ffi_create_window(x: i64, y: i64, w: i64, h: i64,
                      title: text, flags: i64, parent: i64, style: i64):
    ...

# extern fn (separate AST node, not checked)
extern fn rt_create_window(x: i64, y: i64, w: i64, h: i64,
                           title: text, flags: i64, parent: i64, style: i64)
```

### Fixing ARG Warnings

Group related parameters into a struct:

```simple
# Before (warns)
fn create_user(name: text, email: text, age: i64, role: text,
               dept: text, manager: text, office: text, phone: text):
    ...

# After (clean)
struct UserInfo:
    name: text
    email: text
    age: i64
    role: text
    dept: text

fn create_user(info: UserInfo, manager: text, office: text):
    ...
```

---

## Stub Implementation Lint (STUB001/STUB002)

Detects functions with trivial/dummy implementations that may be unintentional stubs.

### STUB001: Trivial Return with Unused Parameters (WARNING)

Fires when a function has parameters but its body is a single trivial expression that doesn't reference any of them.

```simple
# WARNED — params unused, returns bare 0
fn gc_malloc(size: i64) -> i64: 0

# WARNED — params unused, returns empty string
fn load_config(path: text) -> text: ""

# WARNED — params unused, returns false
fn is_supported(feature: text) -> bool: false

# WARNED — params unused, returns Ok(nil)
fn run_backend(module: text) -> Result:
    Ok(nil)
```

### STUB002: Zero-Param Default Return (INFO)

Fires when a zero-parameter function returns a type-default value. Lower confidence since it could be a legitimate constant.

```simple
# INFO — returns default 0 (possible stub)
fn get_count() -> i64: 0

# NOT flagged — non-zero is a legitimate constant
fn max_retries() -> i64: 42

# NOT flagged — non-empty string is a constant
fn method_get() -> text: "GET"

# NOT flagged — true is not a default value
fn is_enabled() -> bool: true
```

### What is NOT Flagged

```simple
# Already marked — pass_todo is explicit
fn not_yet(data: text):
    pass_todo("implement later")

# Already marked — pass_do_nothing is intentional
fn noop_handler(event: text):
    pass_do_nothing

# Self-documenting name — _noop_ prefix suppresses
fn _noop_load(path: text) -> text: ""

# Uses parameters — not a stub
fn identity(x: i64) -> i64: x

# Multi-statement body — not a single-expression stub
fn process(data: text) -> i64:
    val result = parse(data)
    result.len()
```

### Fixing Stub Warnings

For intentional stubs, add a marker:

```simple
# Before (warns)
fn gc_malloc(size: i64) -> i64: 0

# After (suppressed) — intentional no-op
fn gc_malloc(size: i64) -> i64:
    pass_do_nothing  # Runtime uses refcounting, GC not needed
    0

# After (suppressed) — not yet implemented
fn gc_malloc(size: i64) -> i64:
    pass_todo("implement GC allocation")
    0
```

---

## Lint Configuration (`simple.sdn`)

The linter reads project-wide lint levels from `simple.sdn`:

```sdn
[lints]
primitive_api = "warn"
bare_bool = "warn"
export_outside_init = "deny"
too_many_arguments = "warn"
wildcard_match = "allow"
```

### All Configurable Lints

| Name | Default | Description |
|------|---------|-------------|
| `primitive_api` | warn | Bare primitives in public APIs |
| `bare_bool` | warn | Boolean parameters (suggest enum) |
| `print_in_test_spec` | warn | `print()` in test specs |
| `todo_format` | warn | TODO/FIXME format compliance |
| `sspec_no_print_based_tests` | **deny** | Print-based BDD tests |
| `sspec_missing_docstrings` | warn | Missing docstrings in describe/context |
| `sspec_minimal_docstrings` | warn | Too few docstrings in test files |
| `sspec_manual_assertions` | warn | Manual pass/fail instead of expect() |
| `unnamed_duplicate_typed_args` | warn | Same-typed params without names |
| `resource_leak` | warn | Unclosed resources |
| `wildcard_match` | allow | Wildcard `_` in match |
| `non_exhaustive_match` | warn | Missing match arms |
| `export_outside_init` | **deny** | Exports outside `__init__.spl` |
| `init_boundary_violation` | warn | Import bypasses `__init__.spl` |
| `bypass_with_code_files` | warn | `#[bypass]` with sibling code |
| `unknown_decorator` | warn | Unknown `@decorator` |
| `unknown_attribute` | warn | Unknown `#[attribute]` |
| `too_many_arguments` | warn | Functions with >7 params |

### File-Level Overrides

Use attributes to override lint levels per-file:

```simple
#![allow(primitive_api, bare_bool)]   # Inner attribute — file-level

#[allow(too_many_arguments)]          # Outer attribute — file-level (before first definition)
fn complex_fn(a, b, c, d, e, f, g, h):
    ...

#[allow(unknown_annotation)]          # Meta-lint: suppresses both unknown_decorator + unknown_attribute
```

---

## Auto-Fix

```bash
# Preview fixes
bin/simple fix file.spl --dry-run

# Apply safe fixes only
bin/simple fix file.spl

# Apply all fixes (including uncertain)
bin/simple fix file.spl --all

# Interactive mode
bin/simple fix file.spl --interactive
```

---

## Severity Levels

| Level | Behavior |
|-------|----------|
| Deny | Exit code 1, blocks build |
| Warn | Reported, doesn't block by default |
| Allow | Info level, not enforced by default |

Override with flags:

```bash
bin/simple lint file.spl --deny-all    # Treat all warnings as errors
bin/simple lint file.spl --warn-all    # Enable all style lints
```

---

## File Locations

| Component | Path |
|-----------|------|
| Collection lint | `src/compiler/35.semantics/lint/collection_patterns.spl` |
| Duplicate typed args lint | `src/compiler/35.semantics/lint/duplicate_typed_args.spl` |
| Primitive API lint | `src/compiler/35.semantics/lint/primitive_api.spl` |
| Argument count lint (AST) | `src/compiler/35.semantics/lint/argument_count.spl` |
| Argument count lint (Rust) | `src/compiler_rust/compiler/src/lint/checker.rs` |
| Stub impl lint (AST) | `src/compiler/35.semantics/lint/stub_impl.spl` |
| Stub impl lint (text) | `src/compiler/90.tools/fix/rules/impl/lint_stub.spl` |
| EasyFix registry | `src/compiler/90.tools/fix/rules/registry.spl` |
| Semantic linter | `src/compiler/90.tools/lint/main.spl` |
| Diagnostics | `src/compiler/00.common/diagnostics/` |
| Error codes | `src/compiler/00.common/error_codes.spl` |

---

## Related Commands

- `simple build check` — All quality checks
- `simple build fmt` — Code formatting
- `simple duplicate-check` — Code duplication detection
- `simple doc-coverage` — Documentation coverage
