# Call-Site Argument Labels

Call-site labels are postfix keywords attached to arguments at the call site that improve readability of function calls by making the role of each argument explicit. Labels such as `to`, `from`, `by`, `into`, `onto`, and `with` are declared on parameter definitions and optionally used at the call site. Labels are purely syntactic sugar for documentation purposes -- the argument is still matched by position, and omitting the label is valid. This spec validates all six built-in labels, label-free calling, and multi-label combinations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-012 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/call_site_label_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Call-site labels are postfix keywords attached to arguments at the call site that improve
readability of function calls by making the role of each argument explicit. Labels such
as `to`, `from`, `by`, `into`, `onto`, and `with` are declared on parameter definitions
and optionally used at the call site. Labels are purely syntactic sugar for documentation
purposes -- the argument is still matched by position, and omitting the label is valid.
This spec validates all six built-in labels, label-free calling, and multi-label
combinations.

## Syntax

```simple
fn copy_item(src to, dst):
dst
val result = copy_item("a" to, "b")

fn scale(value, factor by):
value * factor
val result = scale(10, 3 by)

fn transfer(amount, src from, dst to):
amount
val result = transfer(100, "checking" from, "savings" to)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Call-Site Label | A postfix keyword (`to`, `from`, `by`, `into`, `onto`, `with`) on an argument |
| Parameter Label | Declared in the function signature after the parameter name |
| Optional Usage | Labels can be omitted at the call site; arguments match by position |
| Multiple Labels | A single function can use different labels on different parameters |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/call_site_label/result.json` |

## Scenarios

- allows to label
- allows from label
- allows by label
- allows into label
- allows onto label
- allows with label
- works without labels
- works with label on param but no label on arg
- supports from and to labels together
