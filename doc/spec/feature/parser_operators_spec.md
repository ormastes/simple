# Parser Operator Specification

**Feature ID:** #PARSER-OP-001 to #PARSER-OP-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/parser_operators_spec.spl`_

---

## Syntax

```simple
# Arithmetic: + - * / % ** //
# Comparison: < > <= >= == !=
# Logical: and or not
# Bitwise: & | ^ ~ << >>
# Pipeline: |> >> <<
# Optional: ?. ?? .?
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 48 |

## Test Structure

### Arithmetic Operator Parsing

- ✅ parses addition
- ✅ parses subtraction
- ✅ parses multiplication
- ✅ parses division
- ✅ parses modulo
- ✅ parses power
- ✅ parses integer division
### Comparison Operator Parsing

- ✅ parses less than
- ✅ parses greater than
- ✅ parses less than or equal
- ✅ parses greater than or equal
- ✅ parses equality
- ✅ parses inequality
### Logical Operator Parsing

- ✅ parses and
- ✅ parses or
- ✅ parses not
- ✅ parses combined logical
### Bitwise Operator Parsing

- ✅ parses bitwise and
- ✅ parses bitwise or
- ✅ parses bitwise xor
- ✅ parses bitwise not
- ✅ parses left shift
- ✅ parses right shift
### Assignment Operator Parsing

- ✅ parses simple assignment
- ✅ parses add-assign
- ✅ parses sub-assign
- ✅ parses mul-assign
- ✅ parses div-assign
- ✅ parses mod-assign
- ✅ parses suspend-assign
### Pipeline Operator Parsing

- ✅ parses pipe forward
### Optional Operator Parsing

- ✅ parses optional chaining
- ✅ parses null coalescing
- ✅ parses existence check
- ✅ parses negated existence
- ✅ parses try operator
### Range Operator Parsing

- ✅ parses exclusive range
- ✅ parses inclusive range
- ✅ parses range in slice
### Operator Precedence Parsing

- ✅ power before multiplication
- ✅ multiplication before addition
- ✅ comparison after arithmetic
- ✅ logical after comparison
- ✅ parentheses override precedence
- ✅ complex expression precedence
### Special Operator Parsing

- ✅ parses matrix multiplication
- ✅ parses broadcast operators
- ✅ parses layer connect

