# Parser Literal Tokenization Specification

**Feature ID:** #PARSER-LIT-001 to #PARSER-LIT-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/parser_literals_spec.spl`_

---

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
r"raw{NL}"        # Raw string (r prefix)
true false      # Booleans
nil             # Nil value
:symbol         # Symbol literal
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 55 |

## Test Structure

### Integer Literal Parsing

#### decimal integers

- ✅ parses simple decimal
- ✅ parses zero
- ✅ parses with underscores
- ✅ parses large numbers
#### hexadecimal integers

- ✅ parses hex with lowercase
- ✅ parses hex with uppercase
- ✅ parses complex hex
#### binary integers

- ✅ parses simple binary
- ✅ parses binary with underscores
- ✅ parses single bit
#### octal integers

- ✅ parses octal
- ✅ parses octal with zeros
### Float Literal Parsing

#### simple floats

- ✅ parses decimal float
- ✅ parses float with leading zero
- ✅ parses whole number float
#### scientific notation

- ✅ parses positive exponent
- ✅ parses negative exponent
- ✅ parses uppercase E
### String Literal Parsing

#### double-quoted strings (interpolated)

- ✅ parses simple string
- ✅ parses escape sequences
- ✅ parses tab escape
- ✅ interpolates variables
- ✅ interpolates expressions
- ✅ escapes braces
#### single-quoted strings (raw)

- ✅ parses raw string
- ✅ does not process escapes
- ✅ does not interpolate
#### raw prefix strings

- ✅ parses r-prefix string
- ✅ keeps backslashes literal
- ✅ keeps braces literal
#### triple-quoted strings

- ✅ parses triple-quoted
- ✅ preserves newlines
- ✅ does not interpolate by default
#### triple-quoted f-strings

- ✅ parses f-prefix triple-quoted
- ✅ interpolates in f-strings
### Boolean Literal Parsing

- ✅ parses true
- ✅ parses false
- ✅ uses booleans in conditions
### Nil Literal Parsing

- ✅ parses nil
- ✅ nil equals nil
### Symbol Literal Parsing

- ✅ parses simple symbol
- ✅ parses symbol with underscore
- ✅ symbols are comparable
### Collection Literal Parsing

#### array literals

- ✅ parses array
- ✅ parses empty array
- ✅ parses nested array
#### tuple literals

- ✅ parses tuple
- ✅ parses unit tuple
- ✅ parses two-element tuple
#### dictionary literals

- ✅ parses dictionary
- ✅ parses empty dictionary
### Numeric Literal Edge Cases

- ✅ parses negative integers
- ✅ parses negative floats
- ✅ parses very small float
- ✅ parses integer with many underscores

