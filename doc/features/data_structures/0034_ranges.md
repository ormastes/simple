# Feature #34: Ranges

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #34 |
| **Feature Name** | Ranges |
| **Category** | Data Structures |
| **Difficulty** | 1 (Trivial) |
| **Status** | Complete |
| **Implementation** | Rust |

## Description

Range expressions for iteration and slicing. Supports inclusive (start..end), exclusive (start..<end), and stepped ranges.

## Specification

[doc/spec/data_structures.md](../../spec/data_structures.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `src/parser/src/expressions/mod.rs` | Range parsing |

## Range Types

| Syntax | Type | Example |
|--------|------|---------|
| start..end | Inclusive | 1..5 = [1,2,3,4,5] |
| start..<end | Exclusive | 1..<5 = [1,2,3,4] |
| start..end by step | Stepped | 0..10 by 2 = [0,2,4,6,8,10] |

## Operations

| Operation | Description |
|-----------|-------------|
| len() | Number of elements |
| contains(v) | Check if v in range |
| to_list() | Convert to list |
| reverse() | Iterate backwards |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/data_structures/ranges_spec.spl` | BDD spec (14 tests) |

## Dependencies

- Depends on: #10
- Required by: None

## Notes

Lazy evaluation for memory efficiency. Step parameter for custom increments. Used with for loops and slice operations.
