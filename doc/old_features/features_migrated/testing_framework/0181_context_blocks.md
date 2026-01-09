# Feature #181: Context Blocks

## Overview

| Property | Value |
|----------|-------|
| **Feature ID** | #181 |
| **Feature Name** | Context Blocks |
| **Category** | Testing Framework |
| **Difficulty** | 2 (Easy) |
| **Status** | Complete |
| **Implementation** | Simple |

## Description

BDD context blocks for creating nested example groups. Provides conditional grouping with when/with semantics for test organization.

## Specification

[doc/spec/testing/testing_bdd_framework.md](../../spec/testing/testing_bdd_framework.md)

## Implementation

### Files

| File | Purpose |
|------|---------|
| `simple/std_lib/src/spec/dsl.spl` | DSL implementation |

## Usage Example

```simple
describe "User":
    context "when logged in":
        it "shows dashboard":
            expect(user.dashboard).to be_visible

    context "when admin":
        it "shows admin panel":
            expect(user.admin_panel).to be_visible
```

## Context Semantics

| Convention | Usage |
|------------|-------|
| `when ...` | Conditional state |
| `with ...` | Fixture/setup |
| `without ...` | Absence of something |
| `given ...` | Precondition |

## Features

| Feature | Description |
|---------|-------------|
| Nesting | Nests inside describe |
| Deep nesting | Multiple levels |
| Inheritance | Inherits parent scope |
| Composition | Combines contexts |

## Testing

### Test Files

| Test File | Description |
|-----------|-------------|
| `simple/std_lib/test/features/testing_framework/context_blocks_spec.spl` | BDD spec (8 tests) |
| `simple/std_lib/test/system/spec/spec_framework_spec.spl` | Framework tests |

## Dependencies

- Depends on: #180
- Required by: #182

## Notes

Alias for nested describe. Supports context composition and reusable context definitions.
