# Parser Error Recovery Specification

**Feature ID:** #PARSER-ERR-001 to #PARSER-ERR-016 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/parser_error_recovery_spec.spl`_

---

## Common Mistakes Detected

- Python: `def`, `None`, `True`, `False`, `self.`
- Rust: `let mut`, `.<T>` turbofish, `!` macros
- TypeScript: `const`, `function`, `let`, `=>`
- Java: `public class`
- C: Type-first declarations (`int x`)

## API

```simple
use std.parser.{Parser, CommonMistake, detect_common_mistake}

val mistake = detect_common_mistake(token, prev_token, next_token)
val message = mistake.message()
val suggestion = mistake.suggestion()
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 38 |

## Test Structure

### Python Syntax Detection

#### def keyword

- ✅ detects Python def
- ✅ suggests fn instead of def
#### None keyword

- ✅ detects Python None in wrong context
- ✅ does not flag None after = (valid Option)
- ✅ suggests nil instead of None
#### True/False keywords

- ✅ detects Python True
- ✅ detects Python False
#### self parameter

- ✅ detects explicit self parameter
- ✅ suggests implicit self
### Rust Syntax Detection

#### let mut

- ✅ detects Rust let mut
- ✅ suggests var instead of let mut
#### turbofish syntax

- ✅ detects Rust turbofish .<T>
#### macro syntax

- ✅ detects Rust macro !
- ✅ suggests @ instead of !
### TypeScript Syntax Detection

#### const keyword

- ✅ detects TypeScript const
- ✅ suggests val instead of const
#### function keyword

- ✅ detects TypeScript function
- ✅ suggests fn instead of function
#### let keyword

- ✅ detects TypeScript let
- ✅ suggests val/var instead of let
#### arrow function

- ✅ detects TypeScript arrow =>
- ✅ suggests lambda instead of arrow
### Java Syntax Detection

#### public class

- ✅ detects Java public class
### C Syntax Detection

#### type-first declaration

- ✅ detects C-style int x
- ✅ detects C-style float y
- ✅ suggests type-after syntax
- ✅ suggests val in suggestion
### Bracket Syntax Detection

#### generic brackets

- ✅ detects wrong brackets for generics
- ✅ suggests angle brackets
### Common Mistake Messages

- ✅ PythonDef message mentions fn
- ✅ PythonNone message mentions nil
- ✅ RustLetMut message mentions var
- ✅ TsConst message mentions val
- ✅ TsFunction message mentions fn
### Common Mistake Suggestions

- ✅ PythonDef suggests fn
- ✅ PythonNone suggests nil
- ✅ RustLetMut suggests var
- ✅ TsConst suggests val

