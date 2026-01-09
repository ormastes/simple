# Feature #183: Before Each Hooks

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #183 |
| **Feature Name** | Before Each Hooks |
| **Category** | Testing Framework |
| **Difficulty** | 2 (Easy) |
| **Status** | Complete |
| **Implementation** | Simple |

## Description

BDD before_each hooks for running setup code before each test example. Ensures consistent test state and reduces duplication.

## Specification

[doc/spec/testing/testing_bdd_framework.md](../../spec/testing/testing_bdd_framework.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `simple/std_lib/src/spec/dsl.spl` | DSL implementation |

## Usage Example

```simple
describe "Calculator":
    before_each:
        let calc = Calculator.new()

    it "starts at zero":
        expect(calc.value).to eq(0)
```

## Hook Behavior

| Behavior | Description |
|----------|-------------|
| Definition order | Runs in order defined |
| Inheritance | Inherits parent hooks |
| Fresh state | Provides clean state |
| Isolation | Each test gets fresh setup |

## Hook Execution Order

1. Parent before_each hooks
2. Child before_each hooks
3. Test body
4. Child after_each hooks
5. Parent after_each hooks

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/testing_framework/before_each_spec.spl` | BDD spec (8 tests) |
| `simple/std_lib/test/system/spec/spec_framework_spec.spl` | Framework tests |

## Dependencies

- Depends on: #180, #181, #182
- Required by: #184

## Notes

Hooks run in definition order. Inherited from parent groups. Runs before each it block.
