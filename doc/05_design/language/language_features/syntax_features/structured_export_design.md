# Structured Export Design

**Date:** 2026-02-01
**Status:** Proposal

## Summary

Replace repetitive `export use` statements in `__init__.spl` files with an indented tree structure that eliminates redundant module path prefixes.

```simple
# Before: repetitive prefixes
export use scanner.scan_directory
export use scanner.scan_tree
export use scanner.ScanResult
export use parser.parse_file
export use parser.ParseResult

# After: structured tree
structured_export:
    scanner:
        scan_directory
        scan_tree
        ScanResult
    parser:
        parse_file
        ParseResult
```

## Motivation

Real example from `src/app/depgraph/__init__.spl` - 20+ lines of `export use` with repeated `scanner.`, `parser.`, `analyzer.`, `generator.` prefixes. The structured form mirrors directory layout and eliminates noise.

Statistics from the codebase:
- 21 `__init__.spl` files in `src/app/`
- Many have 10-30 `export use` statements with repeated prefixes

## Syntax

### Basic Tree

```simple
structured_export:
    module_name:
        symbol1
        symbol2
```

Each leaf desugars to `export use module_name.symbol`.

### Comma-separated Symbols

Related symbols can share a line:

```simple
structured_export:
    mocking_core:
        CallRecord, MockFunction, Expectation
        create_mock, verify_called
```

### Path Scope: Relative to Current Module

**All paths in `structured_export` are relative to the current `__init__.spl`'s module.** They reference direct child modules, not the project root or package name.

```simple
# src/lib/src/testing/__init__.spl
# 'mocking_core' and 'assertions' are direct child modules of 'testing'
structured_export:
    mocking_core:
        MockFunction
        Expectation
    assertions:
        expect, assert_eq
```

Desugars to:
```simple
export use mocking_core.MockFunction
export use mocking_core.Expectation
export use assertions.expect
export use assertions.assert_eq
```

**Not** `export use testing.mocking_core.MockFunction` — `testing` is the current module itself, not a child.

### Nesting for Parent Re-exports

Deeper nesting only applies when a **parent** `__init__.spl` re-exports from a child package:

```simple
# src/lib/src/__init__.spl (parent of testing)
# Here 'testing' IS a child module, so it appears in the tree
structured_export:
    testing:
        mocking_core:
            MockFunction
    collections:
        list, map, set
```

Desugars to:
```simple
export use testing.mocking_core.MockFunction
export use collections.list
export use collections.map
export use collections.set
```

**Rule of thumb:** each `__init__.spl` only references its own direct children. Don't repeat the current module's own name in the tree.

### Mixed with Regular Exports

```simple
# Structured for organized submodules
structured_export:
    scanner:
        scan_directory
        ScanResult

# Regular export for simple cases
export Environment, Scope, Value
```

## Semantics

### Desugar Rules

`structured_export` is pure syntactic sugar. It desugars to `export use` statements before HIR generation:

```simple
# Input
structured_export:
    scanner:
        scan_directory
        ScanResult

# Desugars to
export use scanner.scan_directory
export use scanner.ScanResult
```

### No Implicit Import at Consumer Side

This feature only affects `__init__.spl` authors. Consumers still use explicit `use` statements:

```simple
# Consumer code - unchanged
use crate.app.depgraph.scan_directory
```

### No Wildcards

All exports must be named explicitly. No `scanner.*` syntax in `structured_export`.

## Lint Rules

### `structured_export_placement`

**Severity:** Warning (v0.x), Deny (v1.0)

`structured_export` must appear at the top of `__init__.spl`, after `mod` declarations and `pub mod` statements, before any other code.

```simple
# OK
mod depgraph
pub mod scanner
pub mod parser

structured_export:
    scanner:
        scan_directory

# ERROR: structured_export not at top
mod depgraph
fn helper(): pass

structured_export:  # Warning: must be at top of __init__
    scanner:
        scan_directory
```

### `duplicate_exports`

**Severity:** Deny

Same symbol cannot appear in both `export use` and `structured_export`:

```simple
# ERROR
export use scanner.ScanResult

structured_export:
    scanner:
        ScanResult  # Error: already exported above
```

### `non_existent_export`

**Severity:** Deny

All symbols in `structured_export` must exist in referenced modules.

## Auto-Conversion Tool

```bash
# Preview conversion
simple migrate --to-structured-export --dry-run src/app/

# Convert
simple migrate --to-structured-export src/app/

# Revert
simple migrate --from-structured-export src/app/
```

The tool:
1. Parses `export use` statements
2. Groups by common module prefix
3. Builds indented tree
4. Preserves comments (attaches to nearest group)

## Comparison with Other Languages

| Language | Mechanism | Grouping | Explicit |
|----------|-----------|----------|----------|
| Python | `__all__ = [...]` | No | No (string-based) |
| Rust | `pub use crate::path::Type` | No | Yes |
| TypeScript | `export * from './module'` | No (barrel files) | No (wildcards) |
| Elixir | `alias Module.{A, B, C}` | Limited | Yes |
| **Simple** | `structured_export:` tree | **Yes** | **Yes** |

TypeScript barrel files are widely criticized for causing circular dependencies and performance issues. Simple avoids this by requiring explicit symbol names.

## AST Representation

```rust
struct StructuredExportBlock {
    entries: Vec<StructuredExportEntry>,
    span: Span,
}

struct StructuredExportEntry {
    path: Vec<Ident>,       // module path segments
    symbols: Vec<Ident>,    // exported symbol names
    children: Vec<StructuredExportEntry>,  // nested modules
    span: Span,
}
```

## Edge Cases

### Deep Nesting

Prefer flat namespaces. Deep nesting indicates too many directory layers:

```simple
# Prefer re-exporting at intermediate __init__.spl
# Rather than 5-deep nesting in structured_export
```

### Symbol Name Collisions

Two modules exporting the same name requires aliasing (future feature):

```simple
# Both scanner.Error and parser.Error
export use scanner.Error as ScanError
export use parser.Error as ParseError
```

### When to Use

- **Use `structured_export`** for 10+ exports with repeated prefixes
- **Use `export use`** for 1-3 simple exports
- Both coexist in the same file

## Backward Compatibility

Fully additive. Existing `export use` syntax unchanged. No deprecation planned.

## Implementation Files

- `rust/compiler/src/parser/module.rs` - parse `structured_export` block
- `rust/compiler/src/ast/module.rs` - AST nodes
- `src/app/lint/rules.spl` - lint rules
- `src/app/migrate/` - auto-conversion tool
