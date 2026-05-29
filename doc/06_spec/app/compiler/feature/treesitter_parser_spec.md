# TreeSitter Parser Specification

**Feature ID:** #TS-PARSER-001 to #TS-PARSER-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/treesitter_parser_spec.spl`_

---

## API

```simple
use compiler.treesitter.*

var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 13 |

## Test Structure

### TreeSitter Parser Creation

- ✅ creates parser from source
- ✅ creates parser from empty source
### TreeSitter Basic Function Parsing

- ✅ parses single function
- ✅ parses function with return type
- ✅ parses function with parameters
### TreeSitter Basic Struct Parsing

- ✅ parses struct with fields
### TreeSitter Basic Enum Parsing

- ✅ parses enum with variants
### TreeSitter Import Parsing

- ✅ parses use statement
### TreeSitter Export Parsing

- ✅ parses export statement
### TreeSitter Multi-Declaration Parsing

- ✅ parses function and struct
- ✅ parses function, struct, and enum
### TreeSitter Complex Source Parsing

- ✅ parses function with impl
### TreeSitter Empty Source Parsing

- ✅ returns empty outline for empty source

