# Generic Template Bytecode in SMF

**Feature ID:** #GENERIC-001 | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/usage/generic_bytecode_spec.spl`_

---

## Overview

Tests storage of generic function templates in the SMF (Simple Module Format)
bytecode format. This spec is a placeholder awaiting rewrite from Gherkin DSL
to standard describe/it syntax once the Gherkin feature is production-ready.

## Syntax

```simple
# Generic function stored in .smf
fn identity<T>(x: T) -> T: x
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### Generic Template Bytecode in SMF

- ✅ stores generic function templates in .smf

