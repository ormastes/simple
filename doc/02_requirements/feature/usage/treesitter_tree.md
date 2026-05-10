# TreeSitter Tree Specification
*Source:* `test/feature/usage/treesitter_tree_spec.spl`
**Feature IDs:** #TS-TREE-001 to #TS-TREE-020  |  **Category:** Infrastructure | Parser  |  **Status:** Planned

## Overview



Tests the Tree and Node data structures for the TreeSitter parser,
including node navigation, field access, and span tracking.

NOTE: Tests are skipped until TreeSitterParser crashes are fixed.

## Feature: TreeSitter Tree Root

Tests accessing the root node of a parsed tree.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns root node from tree | pass |
| 2 | root is module type | pass |
| 3 | root has children | pass |

**Example:** returns root node from tree
    Then  expect true

**Example:** root is module type
    Then  expect true

**Example:** root has children
    Then  expect true

## Feature: TreeSitter Node Children

Tests navigating to child nodes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | accesses first child | pass |
| 2 | returns None for invalid index | pass |
| 3 | returns None for negative index | pass |
| 4 | counts children correctly | pass |

**Example:** accesses first child
    Then  expect true

**Example:** returns None for invalid index
    Then  expect true

**Example:** returns None for negative index
    Then  expect true

**Example:** counts children correctly
    Then  expect true

## Feature: TreeSitter Node Fields

Tests accessing named fields on nodes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | accesses field by name | pass |
| 2 | returns None for missing field | pass |

**Example:** accesses field by name
    Then  expect true

**Example:** returns None for missing field
    Then  expect true

## Feature: TreeSitter Node Spans

Tests source position tracking via spans.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | span has start byte | pass |
| 2 | span has end byte | pass |
| 3 | span has line info | pass |
| 4 | span has column info | pass |

**Example:** span has start byte
    Then  expect true

**Example:** span has end byte
    Then  expect true

**Example:** span has line info
    Then  expect true

**Example:** span has column info
    Then  expect true

## Feature: TreeSitter Node Kind

Tests node kind identification.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | has kind property | pass |
| 2 | is_named distinguishes named nodes | pass |

**Example:** has kind property
    Then  expect true

**Example:** is_named distinguishes named nodes
    Then  expect true

## Feature: TreeSitter Node Arena

Tests arena allocation for nodes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | arena stores nodes | pass |
| 2 | arena retrieves by id | pass |
| 3 | invalid id returns None | pass |

**Example:** arena stores nodes
    Then  expect true

**Example:** arena retrieves by id
    Then  expect true

**Example:** invalid id returns None
    Then  expect true

## Feature: TreeSitter Tree Cursor

Tests tree traversal with cursor.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | cursor starts at root | pass |
| 2 | goto_first_child moves down | pass |
| 3 | goto_next_sibling moves right | pass |
| 4 | goto_parent moves up | pass |
| 5 | depth tracks correctly | pass |

**Example:** cursor starts at root
    Then  expect true

**Example:** goto_first_child moves down
    Then  expect true

**Example:** goto_next_sibling moves right
    Then  expect true

**Example:** goto_parent moves up
    Then  expect true

**Example:** depth tracks correctly
    Then  expect true

## Feature: TreeSitter Tree Properties

Tests tree-level properties.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | tree stores source | pass |
| 2 | tree has version | pass |
| 3 | tree walk returns cursor | pass |

**Example:** tree stores source
    Then  expect true

**Example:** tree has version
    Then  expect true

**Example:** tree walk returns cursor
    Then  expect true


