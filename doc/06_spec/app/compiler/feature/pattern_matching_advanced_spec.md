# Advanced Pattern Matching Specification

**Feature ID:** #PAT-ADV-001 to #PAT-ADV-018 | **Category:** Language | Pattern Matching | **Status:** Implemented

_Source: `test/feature/usage/pattern_matching_advanced_spec.spl`_

---

## Syntax

```simple
# Match guards
match x:
    n if n > 0 => "positive"
    n if n < 0 => "negative"
    _ => "zero"

# If val (if let is deprecated)
if val Some(value) = opt:
    print(value)

# While val (while let is deprecated)
while val Some(item) = iterator.next():
    process(item)

# Or patterns
match x:
    1 | 2 | 3 => "small"
    _ => "large"

# Range patterns
match x:
    0..10 => "single digit"
    10..100 => "double digit"
    _ => "large"
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 20 |

## Test Structure

### Match Guards

- ✅ matches with basic guard
- ✅ matches negative with guard
- ✅ uses binding in guard
- ✅ falls through when guard fails
### If Val Expressions

- ✅ matches Some with if val
- ✅ uses else branch for non-matching
- ✅ matches Ok with if val
- ✅ matches Some with if var
### While Let Expressions

- ✅ loops while pattern matches
### Or Patterns

- ✅ matches multiple literals
- ✅ matches medium group
- ✅ falls through to wildcard
### Range Patterns

- ✅ matches exclusive range
- ✅ exclusive range excludes end
- ✅ matches inclusive range
### Numeric Literals

- ✅ parses hex literal
- ✅ hex arithmetic
- ✅ parses binary literal
- ✅ binary with underscores
- ✅ parses octal literal

