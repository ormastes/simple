# TreeSitter Query Specification
*Source:* `test/feature/usage/treesitter_query_spec.spl`
**Feature IDs:** #TS-QUERY-001 to #TS-QUERY-020  |  **Category:** Infrastructure | Parser  |  **Status:** Planned

## Overview




Tests the query system for pattern matching on syntax trees,
including pattern types, captures, and query execution.

NOTE: Tests are skipped until TreeSitterParser crashes are fixed.

## Feature: TreeSitter Query Creation

Tests query initialization for the Simple language.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates query for Simple language | pass |
| 2 | rejects unsupported language | pass |
| 3 | creates query with patterns | pass |
| 4 | creates query with capture names | pass |

**Example:** creates query for Simple language
    Then  expect true

**Example:** rejects unsupported language
    Then  expect true

**Example:** creates query with patterns
    Then  expect true

**Example:** creates query with capture names
    Then  expect true

## Feature: TreeSitter Query Pattern Types

Tests the different types of query patterns.

### Scenario: NodeKind pattern

| # | Example | Status |
|---|---------|--------|
| 1 | creates NodeKind pattern | pass |
| 2 | NodeKind has no capture | pass |

**Example:** creates NodeKind pattern
    Then  expect true

**Example:** NodeKind has no capture
    Then  expect true

### Scenario: CaptureNode pattern

| # | Example | Status |
|---|---------|--------|
| 1 | creates CaptureNode pattern | pass |
| 2 | CaptureNode has capture | pass |

**Example:** creates CaptureNode pattern
    Then  expect true

**Example:** CaptureNode has capture
    Then  expect true

### Scenario: FieldNode pattern

| # | Example | Status |
|---|---------|--------|
| 1 | creates FieldNode pattern | pass |
| 2 | FieldNode is nested | pass |

**Example:** creates FieldNode pattern
    Then  expect true

**Example:** FieldNode is nested
    Then  expect true

### Scenario: ParentNode pattern

| # | Example | Status |
|---|---------|--------|
| 1 | creates ParentNode pattern | pass |
| 2 | ParentNode is nested | pass |

**Example:** creates ParentNode pattern
    Then  expect true

**Example:** ParentNode is nested
    Then  expect true

### Scenario: KeywordList pattern

| # | Example | Status |
|---|---------|--------|
| 1 | creates KeywordList pattern | pass |
| 2 | KeywordList has capture | pass |

**Example:** creates KeywordList pattern
    Then  expect true

**Example:** KeywordList has capture
    Then  expect true

## Feature: TreeSitter Query Pattern Methods

Tests utility methods on QueryPattern.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | converts to string | pass |
| 2 | gets description | pass |
| 3 | gets summary | pass |

**Example:** converts to string
    Then  expect true

**Example:** gets description
    Then  expect true

**Example:** gets summary
    Then  expect true

## Feature: TreeSitter Query Cursor Creation

Tests query cursor initialization.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates cursor with query and tree | pass |
| 2 | cursor executes query on creation | pass |

**Example:** creates cursor with query and tree
    Then  expect true

**Example:** cursor executes query on creation
    Then  expect true

## Feature: TreeSitter Query Execution

Tests query execution and match finding.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | finds matches in tree | pass |
| 2 | returns empty for empty tree | pass |

**Example:** finds matches in tree
    Then  expect true

**Example:** returns empty for empty tree
    Then  expect true

## Feature: TreeSitter Query Match Iteration

Tests the next_match() method.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | iterates matches with next_match | pass |
| 2 | returns None after all matches | pass |

**Example:** iterates matches with next_match
    Then  expect true

**Example:** returns None after all matches
    Then  expect true

## Feature: TreeSitter Query Cursor Reset

Tests the reset() method.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | resets cursor to beginning | pass |
| 2 | can iterate again after reset | pass |

**Example:** resets cursor to beginning
    Then  expect true

**Example:** can iterate again after reset
    Then  expect true

## Feature: TreeSitter Query Match Structure

Tests the structure of QueryResult objects.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | match has pattern index | pass |
| 2 | match has captures list | pass |

**Example:** match has pattern index
    Then  expect true

**Example:** match has captures list
    Then  expect true

## Feature: TreeSitter Capture Structure

Tests the structure of Capture objects.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates capture with name | pass |
| 2 | creates capture with node | pass |
| 3 | creates capture with index | pass |

**Example:** creates capture with name
    Then  expect true

**Example:** creates capture with node
    Then  expect true

**Example:** creates capture with index
    Then  expect true

## Feature: TreeSitter Syntax Highlighting

Tests queries used for syntax highlighting.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | highlights keywords | pass |
| 2 | highlights function names | pass |
| 3 | highlights numbers | pass |

**Example:** highlights keywords
    Then  expect true

**Example:** highlights function names
    Then  expect true

**Example:** highlights numbers
    Then  expect true


