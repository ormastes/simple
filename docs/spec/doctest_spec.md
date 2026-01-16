# Doctest

*Source: `simple/std_lib/test/features/testing_framework/doctest_spec.spl`*

---

# Doctest

**Feature ID:** #192
**Category:** Testing Framework
**Difficulty:** 3/5
**Status:** Complete
**Implementation:** Simple

## Overview

Documentation testing framework that extracts and runs code examples from docstrings. Ensures documentation stays in sync with code by automatically discovering and executing examples embedded in triple-quoted docstrings.

## Syntax

**Docstring Format:**
```simple
fn add(a, b):

return a + b
```

**Running Doctests:**
```simple
# Auto-discover and run all doctests in module
doctest.run_module(my_module)

# Run doctests for specific function
doctest.test_function(add)
```

**Example Syntax:**
- `>>>` prompt indicates code to execute
- Next line shows expected output
- Blank lines separate examples

## Implementation

**Files:**
- `simple/std_lib/src/doctest/__init__.spl` - Main doctest module
- `simple/std_lib/src/doctest/parser.spl` - Docstring parser
- `simple/std_lib/src/doctest/runner.spl` - Test runner

**Test Files:**
- `simple/std_lib/test/system/doctest/parser/parser_spec.spl`

**Dependencies:** #180
**Required By:** None

## Notes

Parses triple-quoted docstrings looking for `>>>` prompts and expected output. Auto-discovers examples in all functions and classes within a module. Helps maintain accurate documentation by verifying examples actually work.
