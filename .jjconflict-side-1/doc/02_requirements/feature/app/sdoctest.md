# SDoctest Specification
*Source:* `test/feature/app/sdoctest_spec.spl`

## Overview



SDoctest is a documentation testing framework for Simple that embeds executable
code examples directly in docstrings. It verifies that documentation examples
remain accurate as code evolves, providing a way to keep examples and code
synchronized without manual effort.


## Usage

    
    ```simple

## Behavior

### Doctest Discovery

Verifies that SDoctest correctly discovers and collects documentation
    examples from module and function docstrings. Tests discovery of examples
    in various documentation locations.

### When function docstring examples

Multiplies two numbers.

            Example 1:
            ```simple
            val r = multiply(3, 4)
            expect r == 12
            ```

            Example 2:
            ```simple
            val r = multiply(0, 100)
            expect r == 0
            ```

- finds examples in function docs
- extracts multiple examples

### When module-level examples

- finds examples in module docs

### Doctest Execution

Verifies that discovered examples are executed correctly during test runs.
    Tests successful execution, assertion verification, and result reporting.

### When successful execution

- executes simple example
- executes example with setup

### When assertion verification

- verifies expect statements
- verifies complex assertions

### When string output verification

- verifies string output

### Doctest Failures

Verifies that SDoctest correctly reports failures in documentation
    examples with useful context for fixing them.

### When assertion failures

- detects failed assertions
- reports wrong output

### When type errors

- catches type mismatches

### Doctest Data Structure Examples

Verifies that doctest examples work correctly with collections,
    custom types, and complex data structures commonly used in code.

### When collection examples

- documents list operations
- documents dict operations

### When custom type examples

- documents custom structs
- documents enums

### Doctest Helpers

Verifies helper functions and setup blocks for doctests that establish
    common fixtures and reduce duplication across examples.

### When helper functions

- uses helper in doctest

### When setup and teardown

- initializes test data

### When multiple examples

- executes related examples


