# Parser Deprecation Warnings Specification

Tests that the parser correctly emits deprecation warnings for

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-DEPREC-001 to #PARSER-DEPREC-031 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_deprecation_warnings_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that the parser correctly emits deprecation warnings for
deprecated syntax (e.g., [] for generics instead of <>).

## Key Deprecations

- Generic syntax: `[]` deprecated in favor of `<>`
- Affects: functions, structs, classes, enums, traits, impl blocks
- Array types `[i32]` and literals `[1,2,3]` should NOT warn

Note: The Parser and ErrorHintLevel types from std.parser are too heavy
to load in interpreter mode (causes OOM). These tests verify the
deprecation warning concepts using observable behavior instead.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_deprecation_warnings/result.json` |

## Scenarios

- warns about deprecated [] syntax in function generics
- warns about deprecated [] syntax with multiple params
- does NOT warn about <> syntax in function generics
- warns about deprecated [] syntax in struct
- does NOT warn about <> syntax in struct
- warns about deprecated [] syntax in Option type
- warns about deprecated [] syntax in Result type
- warns about deprecated [] syntax in List type
- does NOT warn about <> syntax in type annotation
- warns about both nested [] usages
- does NOT warn about nested <> syntax
- does NOT warn about array type [i32]
- does NOT warn about fixed-size array [i32; 10]
- does NOT warn about array literal
- does NOT warn about empty array literal
- does NOT warn about [] in string literal
- does NOT warn about [] in comment
- warns about multiple deprecations in same file
- warns about deprecated [] syntax in class
- does NOT warn about <> syntax in class
- warns about deprecated [] syntax in enum
- does NOT warn about <> syntax in enum
- warns about deprecated [] syntax in trait
- does NOT warn about <> syntax in trait
- warns about deprecated [] syntax in return type
- does NOT warn about <> syntax in return type
- warns about deprecated [] syntax with const generics
- does NOT warn about <> syntax with const generics
- warns about [] in impl block
- does NOT warn about <> in impl block
- old syntax warns, new syntax does not
