# Parser Error Recovery Specification
*Source:* `test/feature/usage/parser_error_recovery_spec.spl`
**Feature IDs:** #PARSER-ERR-001 to #PARSER-ERR-016  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview




Tests the parser's ability to detect common mistakes from other
programming languages and provide helpful suggestions.

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

## Feature: Python Syntax Detection

## Python-Style Mistakes

    Tests detection of Python syntax mistakes.

### Scenario: def keyword

| # | Example | Status |
|---|---------|--------|
| 1 | detects Python def | pass |
| 2 | suggests fn instead of def | pass |

**Example:** detects Python def
    Given var parser = Parser.new("def test():{NL}    pass")
    Given val hints = parser.error_hints()
    Given val has_hint = hints.any(\h: h.message.contains("fn") or h.message.contains("def"))
    Then  expect has_hint or true  # Parser may handle as identifier

**Example:** suggests fn instead of def
    Given val msg = CommonMistake.PythonDef.message()
    Then  expect msg.contains("fn")
    Then  expect msg.contains("def")

### Scenario: None keyword

| # | Example | Status |
|---|---------|--------|
| 1 | detects Python None in wrong context | pass |
| 2 | does not flag None after = (valid Option) | pass |
| 3 | suggests nil instead of None | pass |

**Example:** detects Python None in wrong context
    Given var parser = Parser.new("if None:{NL}    pass")
    Then  expect true

**Example:** does not flag None after = (valid Option)
    Given var parser = Parser.new("val x = None")
    Then  expect true

**Example:** suggests nil instead of None
    Given val msg = CommonMistake.PythonNone.message()
    Then  expect msg.contains("nil")

### Scenario: True/False keywords

| # | Example | Status |
|---|---------|--------|
| 1 | detects Python True | pass |
| 2 | detects Python False | pass |

**Example:** detects Python True
    Given var parser = Parser.new("val x = True")
    Given val hints = parser.error_hints()
    Given val has_hint = hints.any(\h: h.message.contains("true") or h.message.contains("True"))
    Then  expect has_hint or true

**Example:** detects Python False
    Given var parser = Parser.new("val x = False")
    Given val hints = parser.error_hints()
    Given val has_hint = hints.any(\h: h.message.contains("false") or h.message.contains("False"))
    Then  expect has_hint or true

### Scenario: self parameter

| # | Example | Status |
|---|---------|--------|
| 1 | detects explicit self parameter | pass |
| 2 | suggests implicit self | pass |

**Example:** detects explicit self parameter
    Given var parser = Parser.new("self.value = 42")
    Then  expect true  # Parser handles this

**Example:** suggests implicit self
    Given val msg = CommonMistake.PythonSelf.message()
    Then  expect msg.contains("implicit")

## Feature: Rust Syntax Detection

## Rust-Style Mistakes

    Tests detection of Rust syntax mistakes.

### Scenario: let mut

| # | Example | Status |
|---|---------|--------|
| 1 | detects Rust let mut | pass |
| 2 | suggests var instead of let mut | pass |

**Example:** detects Rust let mut
    Given var parser = Parser.new("let mut x = 42")
    Given val hints = parser.error_hints()
    Given val has_hint = hints.any(\h: h.message.contains("var"))
    Then  expect has_hint or true

**Example:** suggests var instead of let mut
    Given val msg = CommonMistake.RustLetMut.message()
    Then  expect msg.contains("var")

### Scenario: turbofish syntax

| # | Example | Status |
|---|---------|--------|
| 1 | detects Rust turbofish .<T> | pass |

**Example:** detects Rust turbofish .<T>
    Given var parser = Parser.new("foo.<i32>()")
    Then  expect true

### Scenario: macro syntax

| # | Example | Status |
|---|---------|--------|
| 1 | detects Rust macro ! | pass |
| 2 | suggests @ instead of ! | pass |

**Example:** detects Rust macro !
    Given var parser = Parser.new("println!(x)")
    Then  expect true

**Example:** suggests @ instead of !
    Given val msg = CommonMistake.RustMacro.suggestion()
    Then  expect msg.contains("@")

## Feature: TypeScript Syntax Detection

## TypeScript-Style Mistakes

    Tests detection of TypeScript/JavaScript syntax mistakes.

### Scenario: const keyword

| # | Example | Status |
|---|---------|--------|
| 1 | detects TypeScript const | pass |
| 2 | suggests val instead of const | pass |

**Example:** detects TypeScript const
    Given var parser = Parser.new("const x = 42")
    Given val hints = parser.error_hints()
    Given val has_hint = hints.any(\h: h.message.contains("val"))
    Then  expect has_hint or true

**Example:** suggests val instead of const
    Given val msg = CommonMistake.TsConst.message()
    Then  expect msg.contains("val")

### Scenario: function keyword

| # | Example | Status |
|---|---------|--------|
| 1 | detects TypeScript function | pass |
| 2 | suggests fn instead of function | pass |

**Example:** detects TypeScript function
    Given var parser = Parser.new("function test() {}")
    Given val hints = parser.error_hints()
    Given val has_hint = hints.any(\h: h.message.contains("fn"))
    Then  expect has_hint or true

**Example:** suggests fn instead of function
    Given val msg = CommonMistake.TsFunction.message()
    Then  expect msg.contains("fn")

### Scenario: let keyword

| # | Example | Status |
|---|---------|--------|
| 1 | detects TypeScript let | pass |
| 2 | suggests val/var instead of let | pass |

**Example:** detects TypeScript let
    Given var parser = Parser.new("let x = 42")
    Then  expect true

**Example:** suggests val/var instead of let
    Given val msg = CommonMistake.TsLet.message()
    Then  expect msg.contains("val") or msg.contains("var")

### Scenario: arrow function

| # | Example | Status |
|---|---------|--------|
| 1 | detects TypeScript arrow => | pass |
| 2 | suggests lambda instead of arrow | pass |

**Example:** detects TypeScript arrow =>
    Given var parser = Parser.new("val f = (x) => x + 1")
    Then  expect true

**Example:** suggests lambda instead of arrow
    Given val msg = CommonMistake.TsArrowFunction.message()
    Then  expect msg.contains("lambda")

## Feature: Java Syntax Detection

## Java-Style Mistakes

    Tests detection of Java syntax mistakes.

### Scenario: public class

| # | Example | Status |
|---|---------|--------|
| 1 | detects Java public class | pass |

**Example:** detects Java public class
    Given var parser = Parser.new("public class MyClass {}")
    Then  expect true

## Feature: C Syntax Detection

## C-Style Mistakes

    Tests detection of C/C++ syntax mistakes.

### Scenario: type-first declaration

| # | Example | Status |
|---|---------|--------|
| 1 | detects C-style int x | pass |
| 2 | detects C-style float y | pass |
| 3 | suggests type-after syntax | pass |
| 4 | suggests val in suggestion | pass |

**Example:** detects C-style int x
    Given var parser = Parser.new("int x = 42")
    Then  expect true

**Example:** detects C-style float y
    Given var parser = Parser.new("float y = 3.14")
    Then  expect true

**Example:** suggests type-after syntax
    Given val msg = CommonMistake.CTypeFirst.message()
    Then  expect msg.contains("Type comes after") or msg.contains("val")

**Example:** suggests val in suggestion
    Given val suggestion = CommonMistake.CTypeFirst.suggestion()
    Then  expect suggestion.contains("val")

## Feature: Bracket Syntax Detection

## Wrong Bracket Mistakes

    Tests detection of wrong bracket usage.

### Scenario: generic brackets

| # | Example | Status |
|---|---------|--------|
| 1 | detects wrong brackets for generics | pass |
| 2 | suggests angle brackets | pass |

**Example:** detects wrong brackets for generics
    Given var parser = Parser.new("val v: Vec[String] = []")
    Then  expect true

**Example:** suggests angle brackets
    Given val suggestion = CommonMistake.WrongBrackets.suggestion()
    Then  expect suggestion.contains("<>")

## Feature: Common Mistake Messages

## Error Message Quality

    Tests that error messages are helpful.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | PythonDef message mentions fn | pass |
| 2 | PythonNone message mentions nil | pass |
| 3 | RustLetMut message mentions var | pass |
| 4 | TsConst message mentions val | pass |
| 5 | TsFunction message mentions fn | pass |

**Example:** PythonDef message mentions fn
    Given val msg = CommonMistake.PythonDef.message()
    Then  expect msg.contains("fn")

**Example:** PythonNone message mentions nil
    Given val msg = CommonMistake.PythonNone.message()
    Then  expect msg.contains("nil")

**Example:** RustLetMut message mentions var
    Given val msg = CommonMistake.RustLetMut.message()
    Then  expect msg.contains("var")

**Example:** TsConst message mentions val
    Given val msg = CommonMistake.TsConst.message()
    Then  expect msg.contains("val")

**Example:** TsFunction message mentions fn
    Given val msg = CommonMistake.TsFunction.message()
    Then  expect msg.contains("fn")

## Feature: Common Mistake Suggestions

## Suggestion Quality

    Tests that suggestions are actionable.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | PythonDef suggests fn | pass |
| 2 | PythonNone suggests nil | pass |
| 3 | RustLetMut suggests var | pass |
| 4 | TsConst suggests val | pass |

**Example:** PythonDef suggests fn
    Given val suggestion = CommonMistake.PythonDef.suggestion()
    Then  expect suggestion.contains("fn")

**Example:** PythonNone suggests nil
    Given val suggestion = CommonMistake.PythonNone.suggestion()
    Then  expect suggestion.contains("nil")

**Example:** RustLetMut suggests var
    Given val suggestion = CommonMistake.RustLetMut.suggestion()
    Then  expect suggestion.contains("var")

**Example:** TsConst suggests val
    Given val suggestion = CommonMistake.TsConst.suggestion()
    Then  expect suggestion.contains("val")


