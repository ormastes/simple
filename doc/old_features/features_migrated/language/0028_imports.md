# Feature #28: Imports

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #28 |
| **Feature Name** | Imports |
| **Category** | Language |
| **Difficulty** | 3 (Medium) |
| **Status** | ✅ Complete |
| **Implementation** | Rust |

## Description

Module system with import statements. Supports importing modules, specific items, and aliased imports.

## Specification

[doc/import_export_and__init__.md](../../doc/import_export_and__init__.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/compiler/src/module_resolver.rs` | Implementation |
| `src/compiler/src/project.rs` | Implementation |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `src/driver/tests/module_tests.rs` | Test suite |

## Dependencies

- Depends on: #1, #2
- Required by: #11, #12

## Notes

Uses __init__.spl for package definitions. Supports relative and absolute imports.
