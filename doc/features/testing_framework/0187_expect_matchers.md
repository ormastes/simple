# Feature #187: Expect Matchers

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #187 |
| **Feature Name** | Expect Matchers |
| **Category** | Testing Framework |
| **Difficulty** | 3 (Medium) |
| **Status** | Complete |
| **Implementation** | Simple |

## Description

BDD expect/to assertion DSL with composable matchers. Provides readable assertions with clear failure messages.

## Specification

[doc/spec/testing/testing_bdd_framework.md](../../spec/testing/testing_bdd_framework.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `simple/std_lib/src/spec/expect.spl` | Expect wrapper |
| `simple/std_lib/src/spec/matchers.spl` | Matcher registry |
| `simple/std_lib/src/spec/matchers/core.spl` | Core matchers |
| `simple/std_lib/src/spec/matchers/comparison.spl` | Comparison matchers |
| `simple/std_lib/src/spec/matchers/collection.spl` | Collection matchers |
| `simple/std_lib/src/spec/matchers/string.spl` | String matchers |

## Available Matchers

| Matcher | Description |
|---------|-------------|
| eq | Equality comparison |
| be | Identity check |
| be_gt | Greater than |
| be_lt | Less than |
| be_gte | Greater or equal |
| be_lte | Less or equal |
| include | Substring check |
| start_with | Prefix check |
| end_with | Suffix check |
| have_length | Collection size |
| be_empty | Empty check |

## Usage Example

```simple
expect(result).to eq(42)
expect(name).to start_with("Hello")
expect(list).to have_length(3)
expect(value).not_to be_nil
```

## Negation

Use `not_to` for negative assertions:
```simple
expect(5).not_to eq(6)
expect(text).not_to include("error")
```

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/testing_framework/expect_matchers_spec.spl` | BDD spec (14 tests) |
| `simple/std_lib/test/system/spec/matchers/spec_matchers_spec.spl` | Matcher tests |

## Dependencies

- Depends on: #182
- Required by: None

## Notes

Supports eq, be, be_gt, be_lt, include, start_with, end_with, have_length, and negation with not_to.
