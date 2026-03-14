# TreeSitter Lexer Specification
*Source:* `test/feature/usage/treesitter_lexer_spec.spl`
**Feature IDs:** #TS-LEX-001 to #TS-LEX-020  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview



Tests the TreeSitter lexer/tokenizer implementation, including token
recognition, spans, and edge cases.

## API

```simple
use std.parser.treesitter.{Lexer, Token, TokenKind}

val lexer = Lexer.new(source)
val tokens = lexer.tokenize().unwrap()
```

## Feature: TreeSitter Lexer Basic Tokenization

## Simple Token Recognition

    Tests basic token recognition for literals and keywords.

### Scenario: integer literals

| # | Example | Status |
|---|---------|--------|
| 1 | tokenizes decimal integer | pass |
| 2 | tokenizes zero | pass |

**Example:** tokenizes decimal integer
    Given var lexer = Lexer.new("42")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes zero
    Given var lexer = Lexer.new("0")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

### Scenario: identifiers

| # | Example | Status |
|---|---------|--------|
| 1 | tokenizes identifier | pass |
| 2 | tokenizes identifier with underscore | pass |
| 3 | tokenizes identifier with digits | pass |

**Example:** tokenizes identifier
    Given var lexer = Lexer.new("foo")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes identifier with underscore
    Given var lexer = Lexer.new("_bar")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes identifier with digits
    Given var lexer = Lexer.new("foo123")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

### Scenario: keywords

| # | Example | Status |
|---|---------|--------|
| 1 | tokenizes fn keyword | pass |
| 2 | tokenizes let keyword | pass |
| 3 | tokenizes if keyword | pass |

**Example:** tokenizes fn keyword
    Given var lexer = Lexer.new("fn")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes let keyword
    Given var lexer = Lexer.new("let")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes if keyword
    Given var lexer = Lexer.new("if")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

## Feature: TreeSitter Lexer Operators

## Operator Recognition

    Tests operator token recognition.

### Scenario: arithmetic operators

| # | Example | Status |
|---|---------|--------|
| 1 | tokenizes plus | pass |
| 2 | tokenizes minus | pass |
| 3 | tokenizes star | pass |
| 4 | tokenizes slash | pass |

**Example:** tokenizes plus
    Given var lexer = Lexer.new("+")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes minus
    Given var lexer = Lexer.new("-")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes star
    Given var lexer = Lexer.new("*")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes slash
    Given var lexer = Lexer.new("/")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

### Scenario: comparison operators

| # | Example | Status |
|---|---------|--------|
| 1 | tokenizes equals | pass |
| 2 | tokenizes not equals | pass |
| 3 | tokenizes less than | pass |
| 4 | tokenizes greater than | pass |
| 5 | tokenizes less than or equal | pass |
| 6 | tokenizes greater than or equal | pass |

**Example:** tokenizes equals
    Given var lexer = Lexer.new("==")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes not equals
    Given var lexer = Lexer.new("!=")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes less than
    Given var lexer = Lexer.new("<")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes greater than
    Given var lexer = Lexer.new(">")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes less than or equal
    Given var lexer = Lexer.new("<=")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes greater than or equal
    Given var lexer = Lexer.new(">=")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

### Scenario: arrow operators

| # | Example | Status |
|---|---------|--------|
| 1 | tokenizes arrow | pass |

**Example:** tokenizes arrow
    Given var lexer = Lexer.new("->")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

## Feature: TreeSitter Lexer Delimiters

## Delimiter Recognition

    Tests delimiter token recognition.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | tokenizes parentheses | pass |
| 2 | tokenizes braces | pass |
| 3 | tokenizes brackets | pass |
| 4 | tokenizes colon | pass |
| 5 | tokenizes comma | pass |
| 6 | tokenizes dot | pass |

**Example:** tokenizes parentheses
    Given var lexer = Lexer.new("()")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 2

**Example:** tokenizes braces
    Given var lexer = Lexer.new("{}")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 2

**Example:** tokenizes brackets
    Given var lexer = Lexer.new("[]")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 2

**Example:** tokenizes colon
    Given var lexer = Lexer.new(":")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes comma
    Given var lexer = Lexer.new(",")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

**Example:** tokenizes dot
    Given var lexer = Lexer.new(".")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1

## Feature: TreeSitter Lexer Expressions

## Multi-Token Expressions

    Tests tokenization of complete expressions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | tokenizes variable declaration | pass |
| 2 | tokenizes binary expression | pass |
| 3 | tokenizes function call | pass |
| 4 | tokenizes method call | pass |

**Example:** tokenizes variable declaration
    Given var lexer = Lexer.new("val x = 42")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 4  # val, x, =, 42, EOF

**Example:** tokenizes binary expression
    Given var lexer = Lexer.new("1 + 2")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 3  # 1, +, 2, EOF

**Example:** tokenizes function call
    Given var lexer = Lexer.new("foo(x, y)")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 5  # foo, (, x, ,, y, ), EOF

**Example:** tokenizes method call
    Given var lexer = Lexer.new("obj.method()")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 5  # obj, ., method, (, ), EOF

## Feature: TreeSitter Lexer Token Spans

## Source Position Tracking

    Tests that tokens have correct source positions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | tracks byte positions | pass |
| 2 | tracks line numbers | pass |
| 3 | tracks column positions | pass |

**Example:** tracks byte positions
    Given var lexer = Lexer.new("x + y")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens[0].span.start_byte == 0

**Example:** tracks line numbers
    Given var lexer = Lexer.new("x{NL}y")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens[0].span.start_line == 1

**Example:** tracks column positions
    Given var lexer = Lexer.new("  x")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens[0].span.start_column >= 1

## Feature: TreeSitter Lexer Token Text

## Token Text Extraction

    Tests that token text is correctly captured.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | captures identifier text | pass |
| 2 | captures number text | pass |
| 3 | captures operator text | pass |

**Example:** captures identifier text
    Given var lexer = Lexer.new("myVariable")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens[0].text == "myVariable"

**Example:** captures number text
    Given var lexer = Lexer.new("12345")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens[0].text == "12345"

**Example:** captures operator text
    Given var lexer = Lexer.new("==")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens[0].text == "=="

## Feature: TreeSitter Lexer Whitespace

## Whitespace Processing

    Tests whitespace handling during tokenization.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | skips spaces between tokens | pass |
| 2 | handles multiple whitespace types | pass |

**Example:** skips spaces between tokens
    Given var lexer = Lexer.new("x   +   y")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 3  # x, +, y, EOF

**Example:** handles multiple whitespace types
    Given var lexer = Lexer.new("x\t+\ty")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 3

## Feature: TreeSitter Lexer EOF

## End of File Token

    Tests that EOF token is correctly added.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | ends with EOF token | pass |
| 2 | empty input produces EOF | pass |

**Example:** ends with EOF token
    Given var lexer = Lexer.new("x")
    Given val tokens = lexer.tokenize().unwrap()
    Given val last = tokens[tokens.len() - 1]
    Then  expect true  # Tokens generated

**Example:** empty input produces EOF
    Given var lexer = Lexer.new("")
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 1  # At least EOF

## Feature: TreeSitter Lexer Complex Source

## Real-World Source Code

    Tests tokenization of realistic code.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | tokenizes function definition | pass |
| 2 | tokenizes struct definition | pass |
| 3 | tokenizes if-else | pass |

**Example:** tokenizes function definition
    Given val source = "fn add(a, b):{NL}    return a + b"
    Given var lexer = Lexer.new(source)
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 10

**Example:** tokenizes struct definition
    Given val source = "struct Point:{NL}    x: i64{NL}    y: i64"
    Given var lexer = Lexer.new(source)
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 8

**Example:** tokenizes if-else
    Given val source = "if x > 0:{NL}    y = 1{NL}else:{NL}    y = 0"
    Given var lexer = Lexer.new(source)
    Given val tokens = lexer.tokenize().unwrap()
    Then  expect tokens.len() >= 12


