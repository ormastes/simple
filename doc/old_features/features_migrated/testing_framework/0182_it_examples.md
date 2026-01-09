# Feature #182: It Examples

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #182 |
| **Feature Name** | It Examples |
| **Category** | Testing Framework |
| **Difficulty** | 2 (Easy) |
| **Status** | Complete |
| **Implementation** | Simple |

## Description

BDD it blocks for defining individual test examples. Each it block represents a single test case with description and assertion block.

## Specification

[doc/spec/testing/testing_bdd_framework.md](../../spec/testing/testing_bdd_framework.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `simple/std_lib/src/spec/dsl.spl` | DSL implementation |

## Usage Example

```simple
it "adds two numbers":
    let result = 1 + 2
    expect(result).to eq(3)

skip "not implemented yet":
    # This test is pending
    pass
```

## Example States

| State | Description |
|-------|-------------|
| Passing | All assertions succeed |
| Failing | Any assertion fails |
| Pending | Marked with skip |
| Errored | Exception thrown |

## Features

| Feature | Description |
|---------|-------------|
| Definition | Creates test case |
| Execution | Runs test body |
| Results | Captures pass/fail |
| Multiple | Supports many assertions |
| Pending | skip for pending tests |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/testing_framework/it_examples_spec.spl` | BDD spec (8 tests) |
| `simple/std_lib/test/system/spec/spec_framework_spec.spl` | Framework tests |

## Dependencies

- Depends on: #180, #181
- Required by: #183, #184

## Notes

Test examples are collected during definition phase. Executed during run phase with proper hook execution.
