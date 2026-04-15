# Parser Literal Tokenization Specification

Tests that the parser correctly tokenizes and parses various literal types

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-LIT-001 to #PARSER-LIT-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_literals_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 55 |
| Active scenarios | 55 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that the parser correctly tokenizes and parses various literal types
including integers, floats, strings, booleans, symbols, and nil.

## Syntax

```simple
42              # Integer
0xFF            # Hex integer
0b1010          # Binary integer
0o77            # Octal integer
3.14            # Float
1.0e10          # Scientific notation
"hello"         # Interpolated string
'raw'           # Raw string
r"raw\n"        # Raw string (r prefix)
true false      # Booleans
nil             # Nil value
:symbol         # Symbol literal
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_literals/result.json` |

## Scenarios

- parses simple decimal
- parses zero
- parses with underscores
- parses large numbers
- parses hex with lowercase
- parses hex with uppercase
- parses complex hex
- parses simple binary
- parses binary with underscores
- parses single bit
- parses octal
- parses octal with zeros
- parses decimal float
- parses float with leading zero
- parses whole number float
- parses positive exponent
- parses negative exponent
- parses uppercase E
- parses simple string
- parses escape sequences
- parses tab escape
- interpolates variables
- interpolates expressions
- escapes braces
- parses raw string
- does not process escapes
- does not interpolate
- parses r-prefix string
- keeps backslashes literal
- keeps braces literal
- parses triple-quoted
- preserves newlines
- does not interpolate by default
- parses f-prefix triple-quoted
- interpolates in f-strings
- parses true
- parses false
- uses booleans in conditions
- parses nil
- nil equals nil
- parses simple symbol
- parses symbol with underscore
- symbols are comparable
- parses array
- parses empty array
- parses nested array
- parses tuple
- parses unit tuple
- parses two-element tuple
- parses dictionary
- parses empty dictionary
- parses negative integers
- parses negative floats
- parses very small float
- parses integer with many underscores
