# Advanced Pattern Matching Specification

Tests advanced pattern matching features including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PAT-ADV-001 to #PAT-ADV-018 |
| Category | Language \| Pattern Matching |
| Status | Implemented |
| Source | `test/feature/usage/pattern_matching_advanced_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests advanced pattern matching features including:
- Match guards (if conditions)
- If let / While let expressions
- Or patterns (|)
- Range patterns (.., ..=)

## Syntax

```simple
match x:
n if n > 0 => "positive"
n if n < 0 => "negative"
_ => "zero"

if val Some(value) = opt:
print(value)

while val Some(item) = iterator.next():
process(item)

match x:
1 | 2 | 3 => "small"
_ => "large"

match x:
0..10 => "single digit"
10..100 => "double digit"
_ => "large"
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/pattern_matching_advanced/result.json` |

## Scenarios

- matches with basic guard
- matches negative with guard
- uses binding in guard
- falls through when guard fails
- matches Some with if val
- uses else branch for non-matching
- matches Ok with if val
- matches Some with if var
- loops while pattern matches
- matches multiple literals
- matches medium group
- falls through to wildcard
- matches exclusive range
- exclusive range excludes end
- matches inclusive range
- parses hex literal
- hex arithmetic
- parses binary literal
- binary with underscores
- parses octal literal
