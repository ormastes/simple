# Access Control with Visibility Modifiers

**Feature ID:** #LANG-038 | **Category:** Language | **Status:** Planned

_Source: `test/feature/usage/visibility_modifiers_spec.spl`_

---

## Overview

Visibility modifiers (`public`, `private`, `protected`) control which scopes may
access a given struct field, class method, or module-level declaration. `public`
members are accessible everywhere, `private` members only within the defining
class or module, and `protected` members within the class and its submodules.
This spec is a placeholder that will be expanded once the visibility modifier
feature is implemented; planned tests will verify compile-time rejection of
illegal access, correct scoping across module boundaries, and interaction with
the existing MDSOC capsule visibility system.

## Syntax

```simple
# Planned visibility modifier syntax (not yet implemented)
class Account:
    private balance: i64
    public fn deposit(amount: i64):
        self.balance = self.balance + amount
    protected fn audit_log(msg: Str):
        print(msg)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `public` | Member is accessible from any scope |
| `private` | Member is accessible only within its declaring class or module |
| `protected` | Member is accessible within its class and submodules |
| Compile-time enforcement | Illegal access should be rejected during compilation, not at runtime |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### Visibility Modifiers

- ✅ placeholder test

