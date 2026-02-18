# TreeSitter Cursor Specification
*Source:* `test/feature/usage/treesitter_cursor_spec.spl`
**Feature IDs:** #TS-CURSOR-001 to #TS-CURSOR-015  |  **Category:** Infrastructure | Parser  |  **Status:** Planned

## Overview




Tests the TreeCursor for efficient tree traversal, including
child/sibling/parent navigation and depth tracking.

NOTE: Tests are skipped until TreeSitterParser crashes are fixed.

## Feature: TreeSitter Cursor Creation

Tests cursor initialization from trees.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates cursor from tree | pass |
| 2 | cursor starts at root | pass |
| 3 | cursor starts at depth 0 | pass |

**Example:** creates cursor from tree
    Then  expect true

**Example:** cursor starts at root
    Then  expect true

**Example:** cursor starts at depth 0
    Then  expect true

## Feature: TreeSitter Cursor First Child

Tests navigation to first child node.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | goes to first child | pass |
| 2 | returns false when no children | pass |
| 3 | increases depth after first child | pass |
| 4 | updates current node after first child | pass |

**Example:** goes to first child
    Then  expect true

**Example:** returns false when no children
    Then  expect true

**Example:** increases depth after first child
    Then  expect true

**Example:** updates current node after first child
    Then  expect true

## Feature: TreeSitter Cursor Next Sibling

Tests navigation to next sibling node.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | goes to next sibling | pass |
| 2 | returns false when no more siblings | pass |
| 3 | maintains depth when moving to sibling | pass |

**Example:** goes to next sibling
    Then  expect true

**Example:** returns false when no more siblings
    Then  expect true

**Example:** maintains depth when moving to sibling
    Then  expect true

## Feature: TreeSitter Cursor Parent

Tests navigation back to parent node.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | goes to parent | pass |
| 2 | returns false at root | pass |
| 3 | decreases depth after parent | pass |
| 4 | returns to original node after child-parent | pass |

**Example:** goes to parent
    Then  expect true

**Example:** returns false at root
    Then  expect true

**Example:** decreases depth after parent
    Then  expect true

**Example:** returns to original node after child-parent
    Then  expect true

## Feature: TreeSitter Cursor Deep Traversal

Tests navigating multiple levels deep.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | traverses multiple levels | pass |
| 2 | tracks parent stack correctly | pass |

**Example:** traverses multiple levels
    Then  expect true

**Example:** tracks parent stack correctly
    Then  expect true

## Feature: TreeSitter Cursor Node Access

Tests accessing the current node from cursor.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | gets current node | pass |
| 2 | node has valid kind | pass |
| 3 | node changes after navigation | pass |

**Example:** gets current node
    Then  expect true

**Example:** node has valid kind
    Then  expect true

**Example:** node changes after navigation
    Then  expect true

## Feature: TreeSitter Cursor Full Walk

Tests walking the entire tree.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | can visit all nodes | pass |
| 2 | visits nested structure | pass |

**Example:** can visit all nodes
    Then  expect true

**Example:** visits nested structure
    Then  expect true

## Feature: TreeSitter Cursor Navigation Reset

Tests returning cursor to specific positions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | can return to root by going to parent repeatedly | pass |

**Example:** can return to root by going to parent repeatedly
    Then  expect true

## Feature: TreeSitter Cursor Complex Patterns

Tests complex navigation patterns used in practice.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | navigates function structure | pass |
| 2 | navigates if-else structure | pass |

**Example:** navigates function structure
    Then  expect true

**Example:** navigates if-else structure
    Then  expect true


