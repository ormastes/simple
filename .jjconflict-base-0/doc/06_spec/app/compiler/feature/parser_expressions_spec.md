# Parser Expression Specification

**Feature ID:** #PARSER-EXPR-001 to #PARSER-EXPR-030 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/parser_expressions_spec.spl`_

---

## Syntax

```simple
# Arithmetic
x + y, x - y, x * y, x / y, x % y, x ** y, x // y

# Comparison
x < y, x > y, x <= y, x >= y, x == y, x != y

# Logical
x and y, x or y, not x

# Method/Field access
obj.method(), obj.field

# Indexing
arr[0], arr[i], arr[1:3]
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 55 |

## Test Structure

### Arithmetic Expression Parsing

#### basic operations

- ✅ parses addition
- ✅ parses subtraction
- ✅ parses multiplication
- ✅ parses division
- ✅ parses modulo
- ✅ parses power
- ✅ parses integer division
#### operator precedence

- ✅ multiplication before addition
- ✅ parentheses override precedence
- ✅ nested parentheses
#### unary operations

- ✅ parses unary minus
- ✅ parses bitwise not
### Comparison Expression Parsing

- ✅ parses less than
- ✅ parses greater than
- ✅ parses less than or equal
- ✅ parses greater than or equal
- ✅ parses equals
- ✅ parses not equals
### Logical Expression Parsing

- ✅ parses and
- ✅ parses or
- ✅ parses not
- ✅ parses combined logical
### Method and Field Access Parsing

#### method calls

- ✅ parses no-arg method call
- ✅ parses method call with args
- ✅ parses chained method calls
#### field access

- ✅ parses field access
- ✅ parses nested field access
### Indexing Expression Parsing

#### simple indexing

- ✅ parses integer index
- ✅ parses variable index
- ✅ parses expression index
- ✅ parses negative index
#### slicing

- ✅ parses start end slice
- ✅ parses end slice
- ✅ parses start slice
### Function Call Expression Parsing

#### positional arguments

- ✅ parses no-arg call
- ✅ parses single arg call
- ✅ parses multi-arg call
#### named arguments

- ✅ parses named arguments
### Path Expression Parsing

- ✅ parses enum variant
- ✅ parses nested path
### Conditional Expression Parsing

- ✅ parses if-else expression
- ✅ parses conditional comparison
### Lambda Expression Parsing

- ✅ parses single parameter lambda
- ✅ parses multi-parameter lambda
- ✅ parses no-parameter lambda
- ✅ uses lambda with map
### is/in Expression Parsing

- ✅ parses is expression
- ✅ parses in expression
- ✅ parses not in expression
### Nested Expression Parsing

- ✅ parses deeply nested arithmetic
- ✅ parses nested collections
- ✅ parses nested method chains
### Optional Chaining Expression Parsing

- ✅ parses optional chaining
- ✅ parses null coalescing
- ✅ parses chained optional access

