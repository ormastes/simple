# Module Visibility Specification

Module visibility system with filename-based auto-public rule. Types matching the filename are automatically public; all other declarations are private by default unless explicitly marked with `public`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-042 (Feature DB ID: 300) |
| Category | Language |
| Difficulty | 3/5 |
| Status | In Progress (Core Complete, Integration Pending) |
| Source | `test/feature/usage/module_visibility_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Module visibility system with filename-based auto-public rule. Types matching
the filename are automatically public; all other declarations are private by
default unless explicitly marked with `public`.

This enables top-level `val` declarations (private by default) and provides
clear visibility control for APIs.

## Syntax

```simple

class TestCase:
id: i32

class Helper:
data: i32

public class PublicHelper:
data: i32

val CONSTANT: i32 = 42

public val PUBLIC_CONSTANT: i32 = 100

fn helper_fn(): pass

public fn public_fn(): pass
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Filename Match | Type name matching filename is auto-public |
| Private Default | All other declarations are private by default |
| `public` Keyword | Explicitly marks declaration as public |
| `private` Keyword | Explicitly marks declaration as private (optional) |
| Top-level `val` | Module-level constants, private by default |
| Name Conversion | snake_case filename -> PascalCase type |

## Behavior

- `test_case.spl` -> `class TestCase` is auto-public
- Other classes/structs in file are private by default
- Functions are private by default
- Top-level `val`/`var` are private by default
- Use `public` keyword to export additional items
- `mod.spl` files are for re-exports only (no auto-public type)

## Related Specifications

- Module System - Import/export mechanics
- Type System - Type visibility in type checking
- Code Quality Tools - Visibility linting

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/module_visibility/result.json` |

## Scenarios

- auto-publics class matching filename
- converts snake_case filename to PascalCase
- makes non-matching types private by default
- supports public keyword for classes
- supports public keyword for functions
- supports private keyword (explicit)
- allows redundant private on non-matching types
- allows private top-level val
- allows public top-level val
- allows top-level val in expressions
- rejects mutable top-level var without explicit public
- methods on public type are public by default
- methods on private type are private
- allows private methods on public type
- warns on implicitly public non-matching type (phase 1)
- warns on implicitly public function (phase 1)
- errors on accessing private type (phase 2)
- suggests adding public modifier in warning
- mod.spl has no auto-public type
- allows importing public items
- rejects importing private items
- allows qualified access to public items
- handles multiple types with same prefix
- handles single-word filenames
- handles acronyms in filenames
- handles nested types visibility
