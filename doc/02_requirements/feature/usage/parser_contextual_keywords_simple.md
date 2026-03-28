# parser contextual keywords simple
*Source:* `test/feature/usage/parser_contextual_keywords_simple_spec.spl`

## Overview

Parser Contextual Keywords - Simplified Tests

Tests contextual keyword behavior for skip, static, and default.
Branch Coverage: 6/6 branches (100%)

## Feature: skip as identifier

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | works as function name | pass |
| 2 | works as method name | pass |

**Example:** works as function name
    Given val result = skip(5)
    Then  expect result == 10

**Example:** works as method name
    Given val obj = MyClass()
    Given val result = obj.skip(10)
    Then  expect result == 11

## Feature: skip as keyword

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | works as standalone statement | pass |
| 2 | works in function body | pass |

**Example:** works as standalone statement
    Then  expect true

**Example:** works in function body
    Then  expect test() == 42

## Feature: static as identifier

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | works as function name | pass |
| 2 | works as method name | pass |

**Example:** works as function name
    Then  expect static() == "static func"

**Example:** works as method name
    Given val cfg = Config()
    Then  expect cfg.static() == 100

## Feature: static as keyword

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | works in static method declaration | pass |

**Example:** works in static method declaration
    Then  expect Math.add(3, 7) == 10

## Feature: default as identifier

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | works as function name | pass |
| 2 | works as method name | pass |

**Example:** works as function name
    Then  expect default() == "default val"

**Example:** works as method name
    Given val settings = Settings()
    Then  expect settings.default() == 200

## Feature: default as keyword

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses in match context | pass |

**Example:** parses in match context
    Given val x = 5
    Given val result = match x:
    Then  expect result == "other"

## Feature: edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows all three keywords as method names in same class | pass |
| 2 | distinguishes keywords from underscored identifiers | pass |

**Example:** allows all three keywords as method names in same class
    Given val obj = Multi()
    Then  expect obj.skip() == 1
    Then  expect obj.static() == 2
    Then  expect obj.default() == 3

**Example:** distinguishes keywords from underscored identifiers
    Given val skip_all = 10
    Given val static_var = 20
    Given val default_value = 30
    Then  expect skip_all == 10
    Then  expect static_var == 20
    Then  expect default_value == 30


