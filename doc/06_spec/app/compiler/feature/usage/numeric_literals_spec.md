# Numeric Literals Specification

Tests for various numeric literal formats including hexadecimal, binary, octal, and numeric separators with underscores.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NUM-001 |
| Category | Language \| Literals |
| Status | Implemented |
| Source | `test/feature/usage/numeric_literals_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for various numeric literal formats including hexadecimal, binary,
octal, and numeric separators with underscores.

## Syntax

```simple
val hex = 0xFF         # Hexadecimal (255)
val bin = 0b1010       # Binary (10)
val oct = 0o755        # Octal (493)
val sep = 1_000_000    # Underscores for readability
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/numeric_literals/result.json` |

## Scenarios

- parses basic hex literal
- parses lowercase hex
- parses mixed case hex
- performs hex arithmetic
- compares hex and decimal
- parses basic binary literal
- parses binary with underscores
- performs binary arithmetic
- uses binary for bit patterns
- parses basic octal literal
- parses small octal
- performs octal arithmetic
- parses decimal with separators
- parses hex with separators
- parses binary with separators
- allows multiple underscores
