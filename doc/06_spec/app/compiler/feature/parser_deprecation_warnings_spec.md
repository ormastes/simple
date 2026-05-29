# Parser Deprecation Warnings Specification

**Feature ID:** #PARSER-DEPREC-001 to #PARSER-DEPREC-031 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/parser_deprecation_warnings_spec.spl`_

---

## Key Deprecations

- Generic syntax: `[]` deprecated in favor of `<>`
- Affects: functions, structs, classes, enums, traits, impl blocks
- Array types `[i32]` and literals `[1,2,3]` should NOT warn

## API

```simple
use std.parser.{Parser, ErrorHint, ErrorHintLevel}

var parser = Parser.new(source)
parser.parse()
val hints = parser.error_hints()
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 31 |

## Test Structure

### Function Generic Deprecation Warnings

- ✅ warns about deprecated [] syntax in function generics
- ✅ warns about deprecated [] syntax with multiple params
- ✅ does NOT warn about <> syntax in function generics
### Struct Generic Deprecation Warnings

- ✅ warns about deprecated [] syntax in struct
- ✅ does NOT warn about <> syntax in struct
### Type Annotation Deprecation Warnings

- ✅ warns about deprecated [] syntax in Option type
- ✅ warns about deprecated [] syntax in Result type
- ✅ warns about deprecated [] syntax in List type
- ✅ does NOT warn about <> syntax in type annotation
### Nested Generic Deprecation Warnings

- ✅ warns about both nested [] usages
- ✅ does NOT warn about nested <> syntax
### Array Type No Deprecation Warnings

- ✅ does NOT warn about array type [i32]
- ✅ does NOT warn about fixed-size array [i32; 10]
### Array Literal No Deprecation Warnings

- ✅ does NOT warn about array literal
- ✅ does NOT warn about empty array literal
### String and Comment No Deprecation Warnings

- ✅ does NOT warn about [] in string literal
- ✅ does NOT warn about [] in comment
### Multiple Deprecation Warnings

- ✅ warns about multiple deprecations in same file

