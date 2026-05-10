# Parser Keywords Specification

**Feature ID:** #PARSER-KW-001 to #PARSER-KW-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/parser_keywords_spec.spl`_

---

use std.text.{NL}

Tests that all Simple language keywords are correctly recognized and
parsed in their appropriate contexts.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 22 |

## Test Structure

### Variable Keyword Parsing

- ✅ val declares immutable variable
- ✅ var declares mutable variable
### Control Flow Keyword Parsing

- ✅ parses if statement
- ✅ parses elif statement
- ✅ parses while loop
- ✅ parses for loop
- ✅ parses break in loop
- ✅ parses continue in loop
- ✅ parses return statement
- ✅ parses match expression
### Logic Keyword Parsing

- ✅ parses and operator
- ✅ parses or operator
- ✅ parses not operator
- ✅ parses in operator
### Special Keyword Parsing

- ✅ parses true
- ✅ parses false
- ✅ parses nil
- ✅ parses self in method
### Function Keyword Parsing

- ✅ parses fn declaration
- ✅ parses nested function
- ✅ parses lambda expression
- ✅ parses higher-order function

