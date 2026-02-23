# TreeSitter OutlineModule Structure Specification

**Feature ID:** #TS-TREE-001 to #TS-TREE-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/treesitter_tree_spec.spl`_

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
| Tests | 14 |

## Test Structure

### OutlineModule Function Parsing

- ✅ parses a simple function
- ✅ parses function with parameters
- ✅ parses extern function
- ✅ parses multiple functions
### OutlineModule Class Parsing

- ✅ parses a simple class
- ✅ parses class fields
### OutlineModule Struct Parsing

- ✅ parses a simple struct
- ✅ parses struct fields
### OutlineModule Enum Parsing

- ✅ parses a simple enum
- ✅ parses enum variants
### OutlineModule Import Parsing

- ✅ parses use statement
- ✅ parses export statement
### OutlineModule Multiple Declarations

- ✅ parses mixed declarations
- ✅ produces empty module for empty source

