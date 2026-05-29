# Dependency Injection Specification

**Feature ID:** #DI-INJ-001 to #DI-INJ-007 | **Category:** Runtime | Dependency Injection | **Status:** Implemented

_Source: `test/feature/usage/di_injection_spec.spl`_

---

**Tags:** di, integration

Integration tests for DI Container with realistic service patterns.
Tests focus on scenarios not covered by unit tests.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 14 |

## Test Structure

### Service with Dependencies

- ✅ creates service with repository dependency
- ✅ chains multiple text dependencies
### Profile-Based Configuration

- ✅ profile enum converts to text
- ✅ profile enum parses from text
- ✅ profile defaults to dev for unknown
- ✅ all profiles have unique names
### Container Binding Pattern

- ✅ stores and retrieves values
- ✅ has returns true for existing keys
- ✅ get returns None for missing keys
- ✅ set overwrites existing values
### DI Error Handling Pattern

- ✅ returns Ok for existing binding
- ✅ returns Err for missing binding
### @inject Decorator Recognition

- ✅ function with @inject is parsed
- ✅ class method with @inject is parsed

