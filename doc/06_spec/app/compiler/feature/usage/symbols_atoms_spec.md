# Symbols and Atoms Specification

Symbols (also called atoms) are immutable, interned identifiers that are compared by identity rather than value. They provide efficient comparison operations and are commonly used for keys, tags, and enum-like values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYMBOLS-001 |
| Category | Language \| Types |
| Status | Implemented |
| Source | `test/feature/usage/symbols_atoms_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/symbols_atoms/result.json` |

## Scenarios

- creates simple symbol
- creates symbol with underscore
- creates multiple distinct symbols
- compares equal symbols
- distinguishes different symbols
- compares symbol in if-else
- compares symbol with not equal
- uses symbol as return value
- uses symbol as function parameter
- uses symbol in conditional logic
- chains symbol checks
