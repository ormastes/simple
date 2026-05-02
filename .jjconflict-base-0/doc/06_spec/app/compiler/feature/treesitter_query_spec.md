# TreeSitter Advanced Outline Parsing Specification

**Feature ID:** #TS-QUERY-001 to #TS-QUERY-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/treesitter_query_spec.spl`_

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
| Tests | 10 |

## Test Structure

### OutlineModule Type Parameters

- ✅ parses struct with type parameter
- ✅ parses class with multiple type parameters
### OutlineModule Trait Parsing

- ✅ parses trait with methods
- ✅ parses empty trait
### OutlineModule Impl Parsing

- ✅ parses impl with methods
- ✅ parses impl with static method
### OutlineModule Type Alias Parsing

- ✅ parses type alias
### OutlineModule Const Parsing

- ✅ parses val declaration
- ✅ parses var declaration
### OutlineModule Mixed Advanced Declarations

- ✅ parses traits and impls together

