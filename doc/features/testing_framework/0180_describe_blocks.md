# Feature #180: Describe Blocks

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #180 |
| **Feature Name** | Describe Blocks |
| **Category** | Testing Framework |
| **Difficulty** | 2 (Easy) |
| **Status** | Complete |
| **Implementation** | Simple |

## Description

BDD describe blocks for grouping related test examples. Creates example groups with descriptions that organize tests hierarchically.

## Specification

[doc/spec/testing/testing_bdd_framework.md](../../spec/testing/testing_bdd_framework.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `simple/std_lib/src/spec/dsl.spl` | DSL implementation |
| `simple/std_lib/src/spec/bdd.spl` | BDD framework |

## Usage Example

```simple
describe "Calculator":
    it "adds numbers":
        expect(1 + 1).to eq(2)

    it "subtracts numbers":
        expect(5 - 3).to eq(2)
```

## Features

| Feature | Description |
|---------|-------------|
| Grouping | Organizes tests by description |
| Nesting | Supports nested groups |
| Registry | Registers with global registry |
| Execution | Runs definition blocks |

## Describe Block Structure

| Component | Purpose |
|-----------|---------|
| Description | Human-readable name |
| Test list | Collection of examples |
| Nested groups | Child describe/context blocks |
| Hooks | Before/after hooks |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/testing_framework/describe_blocks_spec.spl` | BDD spec (10 tests) |
| `simple/std_lib/test/system/spec/spec_framework_spec.spl` | Framework tests |

## Dependencies

- Depends on: None
- Required by: #181, #182

## Notes

Top-level grouping construct. Supports nested context blocks. Registers with global test registry.
