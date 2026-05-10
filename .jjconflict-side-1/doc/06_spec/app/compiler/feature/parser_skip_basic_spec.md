# Skip Keyword - Basic Functionality

**Feature ID:** #PARSER-002 | **Category:** Syntax | **Status:** Active

_Source: `test/feature/usage/parser_skip_basic_spec.spl`_

---

## Overview

Tests basic parsing and runtime behavior of the `skip` keyword as a standalone
statement. Verifies that skip can be used in various contexts (if blocks,
function bodies, loops), that it does not prevent subsequent code execution,
does not affect return values, and does not alter variable scope.

## Syntax

```simple
skip
fn test_function():
    skip
    return "completed"
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### Skip keyword - basic functionality

- ✅ parses skip as standalone statement
- ✅ parses skip with pass
- ✅ parses skip in if block
- ✅ parses skip in function body
- ✅ parses multiple skip statements
- ✅ parses skip before expression
- ✅ parses skip in loop
- ✅ skip does not prevent execution
- ✅ skip does not affect return value
- ✅ skip does not affect variable scope

