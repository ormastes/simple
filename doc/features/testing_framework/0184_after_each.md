# Feature #184: After Each Hooks

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #184 |
| **Feature Name** | After Each Hooks |
| **Category** | Testing Framework |
| **Difficulty** | 2 (Easy) |
| **Status** | Complete |
| **Implementation** | Simple |

## Description

BDD after_each hooks for running cleanup code after each test example. Ensures resources are released and state is cleaned up.

## Specification

[doc/spec/testing/testing_bdd_framework.md](../../spec/testing/testing_bdd_framework.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `simple/std_lib/src/spec/dsl.spl` | DSL implementation |

## Usage Example

```simple
describe "Database":
    after_each:
        db.rollback()
        db.close()

    it "inserts record":
        db.insert(record)
        expect(db.count).to eq(1)
```

## Hook Behavior

| Behavior | Description |
|----------|-------------|
| Guaranteed | Runs even on failure |
| LIFO order | Child hooks run first |
| Cleanup | Release resources |
| Multiple | Supports many hooks |

## Execution Order

After_each hooks run in reverse order (LIFO):
1. Child after_each hooks
2. Parent after_each hooks

This ensures proper resource cleanup.

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/testing_framework/after_each_spec.spl` | BDD spec (8 tests) |
| `simple/std_lib/test/system/spec/spec_framework_spec.spl` | Framework tests |

## Dependencies

- Depends on: #183
- Required by: None

## Notes

Runs after each it block. Runs even if test fails. Child hooks run before parent hooks.
