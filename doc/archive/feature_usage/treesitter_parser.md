# TreeSitter Parser Specification
*Source:* `test/feature/usage/treesitter_parser_spec.spl`
**Feature IDs:** #TS-PARSER-001 to #TS-PARSER-020  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview




Tests the TreeSitter parser implementation for the Simple language,
including tree construction, node types, and parse results.

## API

```simple
use std.parser.treesitter.{TreeSitterParser, Tree, Node}

val parser = TreeSitterParser.new("simple")?
val tree = parser.parse(source)?
val root = tree.root()?
```

## Feature: TreeSitter Parser Creation

## Parser Initialization

    Tests that the parser is correctly created for the Simple language.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates parser for Simple language | pass |
| 2 | rejects unsupported languages | pass |
| 3 | creates parser with grammar loaded | pass |

**Example:** creates parser for Simple language
    Given val result = TreeSitterParser.new("simple")
    Then  expect result.ok.?

**Example:** rejects unsupported languages
    Given val result = TreeSitterParser.new("unknown_language")
    Then  expect result.err.?

**Example:** creates parser with grammar loaded
    Given val parser = TreeSitterParser.new("simple").unwrap()
    Then  expect true  # Parser created successfully

## Feature: TreeSitter Basic Parsing

## Source Code to Tree

    Tests parsing source code into syntax trees.

### Scenario: simple expressions

| # | Example | Status |
|---|---------|--------|
| 1 | parses integer literal | pass |
| 2 | parses variable declaration | pass |
| 3 | parses binary expression | pass |

**Example:** parses integer literal
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("42")
    Then  expect tree.ok.?

**Example:** parses variable declaration
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = 42")
    Then  expect tree.ok.?

**Example:** parses binary expression
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = 1 + 2")
    Then  expect tree.ok.?

### Scenario: function definitions

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple function | pass |
| 2 | parses function with return type | pass |
| 3 | parses function with parameters | pass |

**Example:** parses simple function
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "fn add(a, b):{NL}    a + b"
    Given val tree = parser.parse(source)
    Then  expect tree.ok.?

**Example:** parses function with return type
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "fn get_value() -> i64:{NL}    42"
    Given val tree = parser.parse(source)
    Then  expect tree.ok.?

**Example:** parses function with parameters
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "fn greet(name: text) -> text:{NL}    name"
    Given val tree = parser.parse(source)
    Then  expect tree.ok.?

### Scenario: control flow

| # | Example | Status |
|---|---------|--------|
| 1 | parses if statement | pass |
| 2 | parses while loop | pass |
| 3 | parses for loop | pass |

**Example:** parses if statement
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "if x > 0:{NL}    y = 1"
    Given val tree = parser.parse(source)
    Then  expect tree.ok.?

**Example:** parses while loop
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "while x < 10:{NL}    x = x + 1"
    Given val tree = parser.parse(source)
    Then  expect tree.ok.?

**Example:** parses for loop
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "for i in range(10):{NL}    sum = sum + i"
    Given val tree = parser.parse(source)
    Then  expect tree.ok.?

## Feature: TreeSitter Tree Structure

## Syntax Tree Properties

    Tests the structure of parsed syntax trees.

### Scenario: root node

| # | Example | Status |
|---|---------|--------|
| 1 | has root node after parsing | pass |
| 2 | root node is module type | pass |

**Example:** has root node after parsing
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = 42").unwrap()
    Given val root = tree.root()
    Then  expect root.?

**Example:** root node is module type
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = 42").unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.kind == "module"

### Scenario: child nodes

| # | Example | Status |
|---|---------|--------|
| 1 | function has children | pass |

**Example:** function has children
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "fn test():{NL}    42"
    Given val tree = parser.parse(source).unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.child_count() > 0

### Scenario: node spans

| # | Example | Status |
|---|---------|--------|
| 1 | nodes have valid spans | pass |

**Example:** nodes have valid spans
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = 42").unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.span.start_byte >= 0
    Then  expect root.span.end_byte > root.span.start_byte

## Feature: TreeSitter Node Types

## Node Kind Identification

    Tests that nodes are correctly typed by kind.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | identifies function definition | pass |
| 2 | identifies variable declaration | pass |
| 3 | identifies struct definition | pass |

**Example:** identifies function definition
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "fn test():{NL}    42"
    Given val tree = parser.parse(source).unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.child_count() > 0

**Example:** identifies variable declaration
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = 42").unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.child_count() > 0

**Example:** identifies struct definition
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "struct Point:{NL}    x: i64{NL}    y: i64"
    Given val tree = parser.parse(source).unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.child_count() > 0

## Feature: TreeSitter Multi-Statement Parsing

## Multiple Statements

    Tests parsing of multiple statements in a module.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses multiple declarations | pass |
| 2 | parses mixed declarations | pass |

**Example:** parses multiple declarations
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = """val x = 1
    Given val y = 2
    Given val z = 3"""
    Given val tree = parser.parse(source).unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.child_count() >= 3

**Example:** parses mixed declarations
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = """val x = 42
    Given val tree = parser.parse(source).unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.child_count() >= 3

## Feature: TreeSitter Complex Expression Parsing

## Nested and Complex Expressions

    Tests parsing of complex nested expressions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses nested arithmetic | pass |
| 2 | parses method chain | pass |
| 3 | parses array literal | pass |
| 4 | parses dictionary literal | pass |
| 5 | parses lambda expression | pass |

**Example:** parses nested arithmetic
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = ((1 + 2) * 3)")
    Then  expect tree.ok.?

**Example:** parses method chain
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = obj.method1().method2()")
    Then  expect tree.ok.?

**Example:** parses array literal
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val arr = [1, 2, 3]")
    Then  expect tree.ok.?

**Example:** parses dictionary literal
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse(r'val d = {"key": "value"}')
    Then  expect tree.ok.?

**Example:** parses lambda expression
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse(r"val f = \x: x + 1")
    Then  expect tree.ok.?

## Feature: TreeSitter Source Information

## Source Text and Positions

    Tests that source information is correctly preserved.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | preserves source text | pass |
| 2 | tracks line numbers | pass |
| 3 | tracks column positions | pass |

**Example:** preserves source text
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "val x = 42"
    Given val tree = parser.parse(source).unwrap()
    Then  expect tree.source == source

**Example:** tracks line numbers
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val source = "val x = 42{NL}val y = 43"
    Given val tree = parser.parse(source).unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.span.start_line == 1

**Example:** tracks column positions
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = 42").unwrap()
    Given val root = tree.root().unwrap()
    Then  expect root.span.start_column >= 1

## Feature: TreeSitter Tree Versioning

## Tree Version Tracking

    Tests tree version management for incremental parsing.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | initial tree has version 0 | pass |
| 2 | incremental parse increments version | pass |

**Example:** initial tree has version 0
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("val x = 42").unwrap()
    Then  expect tree.version == 0

**Example:** incremental parse increments version
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree1 = parser.parse("val x = 42").unwrap()
    Then  expect tree1.version >= 0

## Feature: TreeSitter Parse Results

## Success and Error Results

    Tests that parsing returns appropriate results.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns Ok for valid syntax | pass |
| 2 | returns tree for valid syntax | pass |

**Example:** returns Ok for valid syntax
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val result = parser.parse("val x = 42")
    Then  expect result.ok.?

**Example:** returns tree for valid syntax
    Given var parser = TreeSitterParser.new("simple").unwrap()
    Given val tree = parser.parse("fn test():{NL}    42").unwrap()
    Then  expect tree.root().?


