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
