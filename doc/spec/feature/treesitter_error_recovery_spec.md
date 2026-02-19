# TreeSitter Error Handling and Edge Cases Specification

**Feature ID:** #TS-ERR-001 to #TS-ERR-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/treesitter_error_recovery_spec.spl`_

---

## API

```simple
use compiler.treesitter.*

var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
# outline.errors contains ParseError items
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 15 |

## Test Structure

### TreeSitter Edge Cases - Empty Source

- ✅ produces empty module for empty source
- ✅ produces empty module for whitespace only
- ✅ produces empty module for comments only
### TreeSitter Multiple Function Parsing

- ✅ parses three functions
- ✅ preserves function names
### TreeSitter Extern Function Parsing

- ✅ parses extern fn
- ✅ parses extern fn with params
### TreeSitter Method Modifiers

- ✅ parses static method in impl
- ✅ parses mutable method in impl
### TreeSitter Doc Comment Parsing

- ✅ attaches doc comment to function
- ✅ attaches doc comment to struct
### TreeSitter Error Recovery

- ✅ continues parsing after valid declarations
- ✅ parses complex source without crashing
### TreeSitter Trait-Impl Parsing

- ✅ parses trait followed by impl
- ✅ parses impl methods

