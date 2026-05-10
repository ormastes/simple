# call site label
*Source:* `test/feature/usage/call_site_label_spec.spl`

## Overview

use std.text.{NL}
Call-Site Labels Specification

Category: Syntax
Status: Implemented

## Feature: Call-site labels

### Scenario: basic label usage

| # | Example | Status |
|---|---------|--------|
| 1 | allows to label | pass |
| 2 | allows from label | pass |
| 3 | allows by label | pass |
| 4 | allows into label | pass |
| 5 | allows onto label | pass |
| 6 | allows with label | pass |

**Example:** allows to label
    Given val result = copy_item("a" to, "b")
    Then  expect result == "b"

**Example:** allows from label
    Given val result = fetch("http://example.com", "localhost" from)
    Then  expect result == "localhost"

**Example:** allows by label
    Given val result = scale(10, 3 by)
    Then  expect result == 30

**Example:** allows into label
    Given val result = convert("raw", "json" into)
    Then  expect result == "json"

**Example:** allows onto label
    Given val result = place("widget", "canvas" onto)
    Then  expect result == "canvas"

**Example:** allows with label
    Given val result = open_file("/tmp/f", "rw" with)
    Then  expect result == "rw"

### Scenario: no label cases

| # | Example | Status |
|---|---------|--------|
| 1 | works without labels | pass |
| 2 | works with label on param but no label on arg | pass |

**Example:** works without labels
    Given val result = add(3, 4)
    Then  expect result == 7

**Example:** works with label on param but no label on arg
    Given val result = copy_item2("a", "b")
    Then  expect result == "b"

### Scenario: multiple labels

| # | Example | Status |
|---|---------|--------|
| 1 | supports from and to labels together | pass |

**Example:** supports from and to labels together
    Given val result = transfer(100, "checking" from, "savings" to)
    Then  expect result == 100


