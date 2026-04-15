# Parser Function Definition Specification

**Feature ID:** #PARSER-FN-001 to #PARSER-FN-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/parser_functions_spec.spl`_

---

## Syntax

```simple
fn name(params) -> ReturnType:
    body

fn generic<T>(x: T) -> T where T: Trait:
    body

extern fn ffi_func(x: i64) -> i64

macro name(params) -> (contract):
    body
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 33 |

## Test Structure

### Basic Function Definition Parsing

#### minimal functions

- ✅ parses function without params
- ✅ parses function with single param
- ✅ parses function with multiple params
#### return types

- ✅ parses explicit return type
- ✅ parses inferred return
- ✅ parses unit return
#### function body

- ✅ parses multi-statement body
- ✅ parses recursive function
### Generic Function Parsing

- ✅ parses single type parameter
- ✅ parses multiple type parameters
- ✅ parses nested generic types
### Where Clause Parsing

- ✅ parses single where clause
- ✅ parses multiple bounds
- ✅ parses multiple where clauses
### Default Parameter Parsing

- ✅ parses default parameter
- ✅ parses multiple defaults
- ✅ parses mixed required and default
### Named Argument Parsing

- ✅ parses named arguments
- ✅ parses mixed positional and named
- ✅ parses named arguments in any order
### Extern Function Parsing

- ✅ parses extern function
- ✅ parses extern with multiple params
### Macro Definition Parsing

- ✅ parses macro definition
### Actor Definition Parsing

- ✅ parses actor definition
### Method Definition Parsing

#### instance methods

- ✅ parses method with self
- ✅ parses mutable method
#### static methods

- ✅ parses static method
### Lambda Expression Parsing

- ✅ parses simple lambda
- ✅ parses multi-param lambda
- ✅ parses typed lambda
- ✅ parses lambda in higher-order context
### Async Function Parsing

- ✅ parses async function
- ✅ parses await expression

