# Feature #192: Doctest

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #192 |
| **Feature Name** | Doctest |
| **Category** | Testing Framework |
| **Difficulty** | 3 (Medium) |
| **Status** | Complete |
| **Implementation** | Simple |

## Description

Documentation testing framework that extracts and runs code examples from docstrings. Ensures documentation stays in sync with code.

## Specification

[doc/spec/testing/sdoctest.md](../../spec/testing/sdoctest.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `simple/std_lib/src/doctest/__init__.spl` | Doctest module |
| `simple/std_lib/src/doctest/parser.spl` | Example parser |
| `simple/std_lib/src/doctest/runner.spl` | Example runner |

## Usage Example

```simple
fn add(a: Int, b: Int) -> Int:
    """
    Adds two numbers together.

    >>> add(1, 2)
    3
    >>> add(-1, 1)
    0
    """
    return a + b
```

## Prompt Formats

| Prompt | Usage |
|--------|-------|
| `>>>` | Code line |
| `...` | Continuation |
| (none) | Expected output |

## Features

| Feature | Description |
|---------|-------------|
| Parsing | Extracts examples from docstrings |
| Prompts | Recognizes >>> and ... prompts |
| Execution | Runs examples and captures output |
| Discovery | Auto-finds examples in modules |
| Reporting | Shows pass/fail with details |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/testing_framework/doctest_spec.spl` | BDD spec (10 tests) |
| `simple/std_lib/test/system/doctest/parser/parser_spec.spl` | Parser tests |

## Dependencies

- Depends on: #180
- Required by: None

## Notes

Parses triple-quoted docstrings. Supports >>> prompts and expected output. Auto-discovers examples in modules.
