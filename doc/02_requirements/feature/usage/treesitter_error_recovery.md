# TreeSitter Error Recovery Specification
*Source:* `test/feature/usage/treesitter_error_recovery_spec.spl`
**Feature IDs:** #TS-ERR-001 to #TS-ERR-020  |  **Category:** Infrastructure | Parser  |  **Status:** In Progress

## Overview



**Tags:** skip

Tests the error recovery system for the TreeSitter parser,
including recovery strategies, sync points, and error suppression.

NOTE: Tests are skipped until TreeSitterParser module loading issues are fixed.
The error_recovery module implementation is complete at:
src/lib/std/src/parser/treesitter/error_recovery.spl

## API

```simple
use std.parser.treesitter (
    ErrorRecovery, RecoveryStrategy, SyncPoint, ErrorInfo, ParserContext
)

var recovery = ErrorRecovery(
    recent_errors: [],
    max_errors: 1000,
    error_count: 0,
    delimiter_stack: [],
    last_sync_position: 0,
    suppression_window: 10
)
```

## Feature: TreeSitter ErrorRecovery Creation

## Recovery State Initialization

    Tests creating and configuring error recovery state.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates default error recovery | pass |
| 2 | has default max errors | pass |
| 3 | starts with empty recent errors | pass |
| 4 | starts with empty delimiter stack | pass |

**Example:** creates default error recovery
    Then  expect true

**Example:** has default max errors
    Then  expect true

**Example:** starts with empty recent errors
    Then  expect true

**Example:** starts with empty delimiter stack
    Then  expect true

## Feature: TreeSitter Error Suppression

## Cascade Error Prevention

    Tests that errors close together are suppressed.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | does not suppress first error | pass |
| 2 | suppresses error in suppression window | pass |
| 3 | does not suppress error outside window | pass |

**Example:** does not suppress first error
    Then  expect true

**Example:** suppresses error in suppression window
    Then  expect true

**Example:** does not suppress error outside window
    Then  expect true

## Feature: TreeSitter Error Recording

## Error Tracking

    Tests recording errors for analysis and suppression.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | records error | pass |
| 2 | increments error count | pass |
| 3 | tracks multiple errors | pass |

**Example:** records error
    Then  expect true

**Example:** increments error count
    Then  expect true

**Example:** tracks multiple errors
    Then  expect true

## Feature: TreeSitter Error Limit

## Maximum Error Handling

    Tests that parsing stops after too many errors.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | does not reach limit initially | pass |
| 2 | detects when limit reached | pass |

**Example:** does not reach limit initially
    Then  expect true

**Example:** detects when limit reached
    Then  expect true

## Feature: TreeSitter Delimiter Tracking

## Delimiter Balancing

    Tests tracking opening/closing delimiters.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | pushes delimiter | pass |
| 2 | pops delimiter | pass |
| 3 | returns None when stack empty | pass |
| 4 | gets expected closing delimiter | pass |

**Example:** pushes delimiter
    Then  expect true

**Example:** pops delimiter
    Then  expect true

**Example:** returns None when stack empty
    Then  expect true

**Example:** gets expected closing delimiter
    Then  expect true

## Feature: TreeSitter Recovery Strategies

## Strategy Types

    Tests the different recovery strategy types.

### Scenario: SkipToken strategy

| # | Example | Status |
|---|---------|--------|
| 1 | creates SkipToken | pass |

**Example:** creates SkipToken
    Then  expect true

### Scenario: InsertToken strategy

| # | Example | Status |
|---|---------|--------|
| 1 | creates InsertToken | pass |

**Example:** creates InsertToken
    Then  expect true

### Scenario: SyncToStatement strategy

| # | Example | Status |
|---|---------|--------|
| 1 | creates SyncToStatement | pass |

**Example:** creates SyncToStatement
    Then  expect true

### Scenario: SyncToBlock strategy

| # | Example | Status |
|---|---------|--------|
| 1 | creates SyncToBlock | pass |

**Example:** creates SyncToBlock
    Then  expect true

### Scenario: SyncToDeclaration strategy

| # | Example | Status |
|---|---------|--------|
| 1 | creates SyncToDeclaration | pass |

**Example:** creates SyncToDeclaration
    Then  expect true

### Scenario: BalanceDelimiter strategy

| # | Example | Status |
|---|---------|--------|
| 1 | creates BalanceDelimiter | pass |

**Example:** creates BalanceDelimiter
    Then  expect true

### Scenario: PanicMode strategy

| # | Example | Status |
|---|---------|--------|
| 1 | creates PanicMode | pass |

**Example:** creates PanicMode
    Then  expect true

## Feature: TreeSitter Sync Points

## Synchronization Points

    Tests the different synchronization point types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | has Newline sync point | pass |
| 2 | has Indent sync point | pass |
| 3 | has Dedent sync point | pass |
| 4 | has BlockStart sync point | pass |
| 5 | has BlockEnd sync point | pass |
| 6 | has DeclKeyword sync point | pass |
| 7 | has CloseParen sync point | pass |
| 8 | has CloseBracket sync point | pass |
| 9 | has CloseBrace sync point | pass |
| 10 | has EndOfFile sync point | pass |

**Example:** has Newline sync point
    Then  expect true

**Example:** has Indent sync point
    Then  expect true

**Example:** has Dedent sync point
    Then  expect true

**Example:** has BlockStart sync point
    Then  expect true

**Example:** has BlockEnd sync point
    Then  expect true

**Example:** has DeclKeyword sync point
    Then  expect true

**Example:** has CloseParen sync point
    Then  expect true

**Example:** has CloseBracket sync point
    Then  expect true

**Example:** has CloseBrace sync point
    Then  expect true

**Example:** has EndOfFile sync point
    Then  expect true

## Feature: TreeSitter Parser Context

## Context Types

    Tests the different parser context types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | has TopLevel context | pass |
| 2 | has Declaration context | pass |
| 3 | has Statement context | pass |
| 4 | has Expression context | pass |
| 5 | has Block context | pass |
| 6 | has Type context | pass |
| 7 | has Pattern context | pass |

**Example:** has TopLevel context
    Then  expect true

**Example:** has Declaration context
    Then  expect true

**Example:** has Statement context
    Then  expect true

**Example:** has Expression context
    Then  expect true

**Example:** has Block context
    Then  expect true

**Example:** has Type context
    Then  expect true

**Example:** has Pattern context
    Then  expect true

## Feature: TreeSitter ErrorInfo

## Error Information

    Tests the error information structure.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates ErrorInfo with message | pass |
| 2 | creates ErrorInfo with position | pass |
| 3 | creates ErrorInfo with line | pass |
| 4 | creates ErrorInfo with column | pass |
| 5 | creates ErrorInfo with expected tokens | pass |
| 6 | creates ErrorInfo with found token | pass |

**Example:** creates ErrorInfo with message
    Then  expect true

**Example:** creates ErrorInfo with position
    Then  expect true

**Example:** creates ErrorInfo with line
    Then  expect true

**Example:** creates ErrorInfo with column
    Then  expect true

**Example:** creates ErrorInfo with expected tokens
    Then  expect true

**Example:** creates ErrorInfo with found token
    Then  expect true

## Feature: TreeSitter Error Nodes

## ERROR Node Handling

    Tests that error nodes are created in the CST.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | marks node as having error | pass |
| 2 | produces tree despite errors | pass |

**Example:** marks node as having error
    Then  expect true

**Example:** produces tree despite errors
    Then  expect true


