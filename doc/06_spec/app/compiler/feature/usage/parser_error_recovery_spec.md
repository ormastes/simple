# Parser Error Recovery Specification

Tests the parser's ability to detect common mistakes from other

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-ERR-001 to #PARSER-ERR-016 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_error_recovery_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests the parser's ability to detect common mistakes from other
programming languages and provide helpful suggestions.

## Common Mistakes Detected

- Python: `def`, `None`, `True`, `False`, `self.`
- Rust: `let mut`, `.<T>` turbofish, `!` macros
- TypeScript: `const`, `function`, `let`, `=>`
- Java: `public class`
- C: Type-first declarations (`int x`)

## API

```simple
use std.parser.{Parser, CommonMistake, detect_common_mistake}

val mistake = detect_common_mistake(token, prev_token, next_token)
val message = mistake.message()
val suggestion = mistake.suggestion()
```

Note: The Parser and CommonMistake types are compiler-internal constructs.
In interpreter mode, the std.parser module provides data format parsing
(JSON, CSV, etc.), not the compiler parser. These tests verify the concepts
are documented; actual parser error recovery is tested via compiled mode.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_error_recovery/result.json` |

## Scenarios

- detects Python def
- suggests fn instead of def
- detects Python None in wrong context
- does not flag None after = (valid Option)
- suggests nil instead of None
- detects Python True
- detects Python False
- detects explicit self parameter
- suggests implicit self
- detects Rust let mut
- suggests var instead of let mut
- detects Rust turbofish .<T>
- detects Rust macro !
- suggests @ instead of !
- detects TypeScript const
- suggests val instead of const
- detects TypeScript function
- suggests fn instead of function
- detects TypeScript let
- suggests val/var instead of let
- detects TypeScript arrow =>
- suggests lambda instead of arrow
- detects Java public class
- detects C-style int x
- detects C-style float y
- suggests type-after syntax
- suggests val in suggestion
- detects wrong brackets for generics
- suggests angle brackets
- PythonDef message mentions fn
- PythonNone message mentions nil
- RustLetMut message mentions var
- TsConst message mentions val
- TsFunction message mentions fn
- PythonDef suggests fn
- PythonNone suggests nil
- RustLetMut suggests var
- TsConst suggests val
