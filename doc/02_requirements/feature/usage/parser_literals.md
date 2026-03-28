# Parser Literal Tokenization Specification
*Source:* `test/feature/usage/parser_literals_spec.spl`
**Feature IDs:** #PARSER-LIT-001 to #PARSER-LIT-020  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview




Tests that the parser correctly tokenizes and parses various literal types
including integers, floats, strings, booleans, symbols, and nil.

## Syntax

```simple
42              # Integer
0xFF            # Hex integer
0b1010          # Binary integer
0o77            # Octal integer
3.14            # Float
1.0e10          # Scientific notation
"hello"         # Interpolated string
'raw'           # Raw string
r"raw{NL}"        # Raw string (r prefix)
true false      # Booleans
nil             # Nil value
:symbol         # Symbol literal
```

## Feature: Integer Literal Parsing

## Decimal, Hex, Binary, Octal

    Tests that integer literals in various bases are correctly parsed.

### Scenario: decimal integers

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple decimal | pass |
| 2 | parses zero | pass |
| 3 | parses with underscores | pass |
| 4 | parses large numbers | pass |

**Example:** parses simple decimal
    Given val x = 42
    Then  expect x == 42

**Example:** parses zero
    Given val x = 0
    Then  expect x == 0

**Example:** parses with underscores
    Given val x = 1_000_000
    Then  expect x == 1000000

**Example:** parses large numbers
    Given val x = 9_223_372_036_854_775_807
    Then  expect x > 0

### Scenario: hexadecimal integers

| # | Example | Status |
|---|---------|--------|
| 1 | parses hex with lowercase | pass |
| 2 | parses hex with uppercase | pass |
| 3 | parses complex hex | pass |

**Example:** parses hex with lowercase
    Given val x = 0xff
    Then  expect x == 255

**Example:** parses hex with uppercase
    Given val x = 0xFF
    Then  expect x == 255

**Example:** parses complex hex
    Given val x = 0x1A2B
    Then  expect x == 6699

### Scenario: binary integers

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple binary | pass |
| 2 | parses binary with underscores | pass |
| 3 | parses single bit | pass |

**Example:** parses simple binary
    Given val x = 0b1010
    Then  expect x == 10

**Example:** parses binary with underscores
    Given val x = 0b1111_0000
    Then  expect x == 240

**Example:** parses single bit
    Given val x = 0b1
    Then  expect x == 1

### Scenario: octal integers

| # | Example | Status |
|---|---------|--------|
| 1 | parses octal | pass |
| 2 | parses octal with zeros | pass |

**Example:** parses octal
    Given val x = 0o77
    Then  expect x == 63

**Example:** parses octal with zeros
    Given val x = 0o755
    Then  expect x == 493

## Feature: Float Literal Parsing

## Decimal and Scientific Notation

    Tests floating point literal parsing including scientific notation.

### Scenario: simple floats

| # | Example | Status |
|---|---------|--------|
| 1 | parses decimal float | pass |
| 2 | parses float with leading zero | pass |
| 3 | parses whole number float | pass |

**Example:** parses decimal float
    Given val x = 3.14
    Then  expect x > 3.0
    Then  expect x < 4.0

**Example:** parses float with leading zero
    Given val x = 0.5
    Then  expect x == 0.5

**Example:** parses whole number float
    Given val x = 1.0
    Then  expect x == 1.0

### Scenario: scientific notation

| # | Example | Status |
|---|---------|--------|
| 1 | parses positive exponent | pass |
| 2 | parses negative exponent | pass |
| 3 | parses uppercase E | pass |

**Example:** parses positive exponent
    Given val x = 1.0e10
    Then  expect x == 10000000000.0

**Example:** parses negative exponent
    Given val x = 2.5e-3
    Then  expect x < 0.003

**Example:** parses uppercase E
    Given val x = 1.5E5
    Then  expect x == 150000.0

## Feature: String Literal Parsing

## Interpolated, Raw, and Triple-Quoted Strings

    Tests string literal parsing with escape sequences and interpolation.

### Scenario: double-quoted strings (interpolated)

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple string | pass |
| 2 | parses escape sequences | pass |
| 3 | parses tab escape | pass |
| 4 | interpolates variables | pass |
| 5 | interpolates expressions | pass |
| 6 | escapes braces | pass |

**Example:** parses simple string
    Given val s = "hello"
    Then  expect s == "hello"

**Example:** parses escape sequences
    Given val s = "hello{NL}world"
    Then  expect s.contains("{NL}")

**Example:** parses tab escape
    Given val s = "tab\there"
    Then  expect s.contains("\t")

**Example:** interpolates variables
    Given val name = "Alice"
    Given val s = "hello {name}"
    Then  expect s == "hello Alice"

**Example:** interpolates expressions
    Given val x = 6
    Given val y = 7
    Given val s = "result: {x * y}"
    Then  expect s == "result: 42"

**Example:** escapes braces
    Given val s = "literal {{braces}}"
    Then  expect s == r"literal {braces}"

### Scenario: single-quoted strings (raw)

| # | Example | Status |
|---|---------|--------|
| 1 | parses raw string | pass |
| 2 | does not process escapes | pass |
| 3 | does not interpolate | pass |

**Example:** parses raw string
    Given val s = 'hello'
    Then  expect s == "hello"

**Example:** does not process escapes
    Given val s = 'hello{NL}world'
    Then  expect s.contains("\{NL}")

**Example:** does not interpolate
    Given val s = '{name}'
    Then  expect s == r"{name}"

### Scenario: raw prefix strings

| # | Example | Status |
|---|---------|--------|
| 1 | parses r-prefix string | pass |
| 2 | keeps backslashes literal | pass |
| 3 | keeps braces literal | pass |

**Example:** parses r-prefix string
    Given val s = r"hello"
    Then  expect s == "hello"

**Example:** keeps backslashes literal
    Given val s = r"hello{NL}world"
    Then  expect s.contains("\{NL}")

**Example:** keeps braces literal
    Given val s = r"{name}"
    Then  expect s == r"{name}"

### Scenario: triple-quoted strings

| # | Example | Status |
|---|---------|--------|
| 1 | parses triple-quoted | pass |
| 2 | preserves newlines | pass |
| 3 | does not interpolate by default | pass |

**Example:** parses triple-quoted
    Given val s = """hello"""
    Then  expect s == "hello"

**Example:** preserves newlines
    Given val s = """line1
    Then  expect s.contains("{NL}")

**Example:** does not interpolate by default
    Given val s = """{name}"""
    Then  expect s == r"{name}"

### Scenario: triple-quoted f-strings

| # | Example | Status |
|---|---------|--------|
| 1 | parses f-prefix triple-quoted | pass |
| 2 | interpolates in f-strings | pass |

**Example:** parses f-prefix triple-quoted
    Given val s = f"""hello"""
    Then  expect s == "hello"

**Example:** interpolates in f-strings
    Given val name = "world"
    Given val s = f"""hello {name}"""
    Then  expect s == "hello world"

## Feature: Boolean Literal Parsing

## true and false Keywords

    Tests that boolean literals are correctly parsed.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses true | pass |
| 2 | parses false | pass |
| 3 | uses booleans in conditions | pass |

**Example:** parses true
    Given val x = true
    Then  expect x == true

**Example:** parses false
    Given val x = false
    Then  expect x == false

**Example:** uses booleans in conditions
    Given val condition = true
    Then  expect true
    Then  expect false  # Should not reach

## Feature: Nil Literal Parsing

## nil Keyword

    Tests that the nil literal is correctly parsed.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses nil | pass |
| 2 | nil equals nil | pass |

**Example:** parses nil
    Given val x = nil
    Then  expect x == nil

**Example:** nil equals nil
    Then  expect nil == nil

## Feature: Symbol Literal Parsing

## :symbol Syntax

    Tests that symbol literals with colon prefix are correctly parsed.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple symbol | pass |
| 2 | parses symbol with underscore | pass |
| 3 | symbols are comparable | pass |

**Example:** parses simple symbol
    Given val s = :ok
    Then  expect s == :ok

**Example:** parses symbol with underscore
    Given val s = :error_code
    Then  expect s == :error_code

**Example:** symbols are comparable
    Then  expect :ok == :ok
    Then  expect :ok != :error

## Feature: Collection Literal Parsing

## Arrays, Tuples, and Dictionaries

    Tests parsing of collection literal syntax.

### Scenario: array literals

| # | Example | Status |
|---|---------|--------|
| 1 | parses array | pass |
| 2 | parses empty array | pass |
| 3 | parses nested array | pass |

**Example:** parses array
    Given val arr = [1, 2, 3]
    Then  expect arr.len() == 3

**Example:** parses empty array
    Given val arr = []
    Then  expect arr.len() == 0

**Example:** parses nested array
    Given val arr = [[1, 2], [3, 4]]
    Then  expect arr[0][1] == 2

### Scenario: tuple literals

| # | Example | Status |
|---|---------|--------|
| 1 | parses tuple | pass |
| 2 | parses unit tuple | pass |
| 3 | parses two-element tuple | pass |

**Example:** parses tuple
    Given val t = (1, 2, 3)
    Then  expect t.0 == 1

**Example:** parses unit tuple
    Given val t = ()
    Then  expect true  # Compiles successfully

**Example:** parses two-element tuple
    Given val t = (42, "hello")
    Then  expect t.0 == 42

### Scenario: dictionary literals

| # | Example | Status |
|---|---------|--------|
| 1 | parses dictionary | pass |
| 2 | parses empty dictionary | pass |

**Example:** parses dictionary
    Given val d = {"a": 1, "b": 2}
    Then  expect d["a"] == 1

**Example:** parses empty dictionary
    Given val d = {}
    Then  expect d.len() == 0

## Feature: Numeric Literal Edge Cases

## Special Cases and Boundaries

    Tests edge cases in numeric literal parsing.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses negative integers | pass |
| 2 | parses negative floats | pass |
| 3 | parses very small float | pass |
| 4 | parses integer with many underscores | pass |

**Example:** parses negative integers
    Given val x = -42
    Then  expect x == -42

**Example:** parses negative floats
    Given val x = -3.14
    Then  expect x < 0.0

**Example:** parses very small float
    Given val x = 0.000001
    Then  expect x > 0.0

**Example:** parses integer with many underscores
    Given val x = 1_2_3_4_5
    Then  expect x == 12345


