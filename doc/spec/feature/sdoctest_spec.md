# SDoctest Specification

**Feature ID:** #SDOCTEST | **Category:** Tooling | **Status:** Implemented

_Source: `test/feature/app/sdoctest_spec.spl`_

---

## Syntax

```simple

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 18 |

## Test Structure

### Doctest Discovery

#### function docstring examples

- ✅ finds examples in function docs
- ✅ extracts multiple examples
#### module-level examples

- ✅ finds examples in module docs
### Doctest Execution

#### successful execution

- ✅ executes simple example
- ✅ executes example with setup
#### assertion verification

- ✅ verifies expect statements
- ✅ verifies complex assertions
#### string output verification

- ✅ verifies string output
### Doctest Failures

#### assertion failures

- ✅ detects failed assertions
- ✅ reports wrong output
#### type errors

- ✅ catches type mismatches
### Doctest Data Structure Examples

#### collection examples

- ✅ documents list operations
- ✅ documents dict operations
#### custom type examples

- ✅ documents custom structs
- ✅ documents enums
### Doctest Helpers

#### helper functions

- ✅ uses helper in doctest
#### setup and teardown

- ✅ initializes test data
#### multiple examples

- ✅ executes related examples

