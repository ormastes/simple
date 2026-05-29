# Numeric Literals Specification

**Feature ID:** #NUM-001 | **Category:** Language | Literals | **Status:** Implemented

_Source: `test/feature/usage/numeric_literals_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 16 |

## Test Structure

### Hexadecimal Literals

- ✅ parses basic hex literal
- ✅ parses lowercase hex
- ✅ parses mixed case hex
- ✅ performs hex arithmetic
- ✅ compares hex and decimal
### Binary Literals

- ✅ parses basic binary literal
- ✅ parses binary with underscores
- ✅ performs binary arithmetic
- ✅ uses binary for bit patterns
### Octal Literals

- ✅ parses basic octal literal
- ✅ parses small octal
- ✅ performs octal arithmetic
### Numeric Separators

- ✅ parses decimal with separators
- ✅ parses hex with separators
- ✅ parses binary with separators
- ✅ allows multiple underscores

