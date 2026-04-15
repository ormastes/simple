# Set Literal Syntax

Tests the `s{...}` set literal syntax for creating sets with automatic duplicate removal. Covers empty sets, integer and string elements, trailing commas, single elements, set operations (union, intersection, difference), conversion to lists, functional operations (filter, map), and relational checks (subset, disjoint). Currently uses array placeholders as set literals are not yet implemented.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-003 |
| Category | Syntax |
| Status | In Progress |
| Source | `test/feature/usage/set_literal_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the `s{...}` set literal syntax for creating sets with automatic duplicate
removal. Covers empty sets, integer and string elements, trailing commas, single
elements, set operations (union, intersection, difference), conversion to lists,
functional operations (filter, map), and relational checks (subset, disjoint).
Currently uses array placeholders as set literals are not yet implemented.

## Syntax

```simple
val nums = s{1, 2, 3}
val union_set = a.union(b)
val evens = nums.filter(\x: x % 2 == 0)
```
Set Literal Tests

Test set literal syntax: s{1, 2, 3}

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/set_literal/result.json` |

## Scenarios

- creates empty set
- creates set from integer elements
- removes duplicates automatically
- creates set from string elements
- handles trailing comma
- supports single element
- computes union via concatenation
- computes intersection via filter
- computes difference via filter
- supports filter
- supports map
- checks subset via all-contained
- checks disjoint via no overlap
