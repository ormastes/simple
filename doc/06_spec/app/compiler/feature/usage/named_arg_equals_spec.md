# Named Argument with Equals Syntax Specification

Named arguments allow passing function arguments by name rather than position.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NAMED-ARG-EQUALS |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/named_arg_equals_spec.spl` |
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

Named arguments allow passing function arguments by name rather than position.
Simple supports both colon syntax `name: value` and equals syntax `name=value`
for named arguments, providing flexibility in coding style.

## Syntax

```simple
connect(host: "localhost", port: 8080)

Point(x=3, y=4)

greet("Hello", name="World")
```

## Key Behaviors

- Named arguments can appear in any order
- Named arguments can be mixed with positional arguments
- Positional arguments must come before named arguments
- Both `name: value` and `name=value` syntax are supported

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/named_arg_equals/result.json` |

## Scenarios

- passes single named argument
- passes multiple named arguments
- allows reordered named arguments
- passes single named argument with colon
- passes multiple named arguments with colon
- allows reordered named arguments with colon
- combines positional with named equals
- combines positional with named colon
- uses multiple positional then named
- uses default when named arg omitted
- overrides default with named arg
- overrides multiple defaults
- overrides defaults in any order
- constructs struct with equals syntax
- constructs struct with colon syntax
- allows reordered struct fields
- constructs complex struct
- handles single character parameter names
- handles longer parameter names
- handles underscored parameter names
