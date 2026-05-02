# Symbols and Atoms Specification

**Feature ID:** #SYMBOLS-001 | **Category:** Language | Types | **Status:** Implemented

_Source: `test/feature/usage/symbols_atoms_spec.spl`_

---

## Overview

Symbols (also called atoms) are immutable, interned identifiers that are
compared by identity rather than value. They provide efficient comparison
operations and are commonly used for keys, tags, and enum-like values.

## Syntax

```simple
val status = :ok
val error = :not_found

if status is :ok:
    handle_success()
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Symbol | Interned identifier compared by identity |
| Atom | Alternative name for symbol (Erlang terminology) |
| Interning | Process of storing unique string once |
| Symbol Table | Runtime storage for interned symbols |

## Behavior

- Symbols are prefixed with colon: `:name`
- Symbol comparison is O(1) pointer equality
- All occurrences of same symbol share memory
- Symbols are immutable and cannot be modified

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 11 |

## Test Structure

### Symbol Creation

- ✅ creates simple symbol
- ✅ creates symbol with underscore
- ✅ creates multiple distinct symbols
### Symbol Comparison

- ✅ compares equal symbols
- ✅ distinguishes different symbols
- ✅ compares symbol in if-else
- ✅ compares symbol with not equal
### Symbol Use Cases

- ✅ uses symbol as return value
- ✅ uses symbol as function parameter
- ✅ uses symbol in conditional logic
- ✅ chains symbol checks

