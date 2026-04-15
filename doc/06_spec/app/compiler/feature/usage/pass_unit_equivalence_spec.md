# Pass Statement and Unit Value Equivalence

In Simple, the `pass` keyword and the unit literal `()` are semantically equivalent -- both represent a deliberate no-operation and compile to the same code. This spec proves their interchangeability in every statement position: standalone expressions, if/else branches, and loop bodies. It also documents the style guideline that `pass` is preferred when the programmer wants to signal explicit "do nothing" intent, while `()` is the underlying unit value.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-021 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/pass_unit_equivalence_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

In Simple, the `pass` keyword and the unit literal `()` are semantically
equivalent -- both represent a deliberate no-operation and compile to the same
code. This spec proves their interchangeability in every statement position:
standalone expressions, if/else branches, and loop bodies. It also documents the
style guideline that `pass` is preferred when the programmer wants to signal
explicit "do nothing" intent, while `()` is the underlying unit value.

## Syntax

```simple
pass
x = 1

()
x = 1

if x == 10:
branch_taken = "ten"
else:
pass
branch_taken = "other"

for i in [0, 1, 2]:
if i == 1:
pass
count = count + 1
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `pass` | A no-op keyword signalling intentional emptiness, analogous to Python's `pass` |
| `()` | The unit literal, representing the absence of a meaningful value |
| Equivalence | `pass` and `()` produce identical compiled output in all statement positions |
| Style guideline | Use `pass` for explicit no-op intent; use `()` when a unit value is needed |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/pass_unit_equivalence/result.json` |

## Scenarios

- both work as standalone statements
- both work in if-else branches
- both work in loops
- documents that pass is no-op statement
- recommends pass for explicit no-op intent
