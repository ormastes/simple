# SMF note.sdn Instantiation Tracking

**Feature ID:** #GENERIC-002 | **Category:** Compiler | **Status:** In Progress

_Source: `test/feature/usage/note_sdn_feature_spec.spl`_

---

## Overview

Tests the note.sdn section in SMF (Simple Module Format) for tracking generic
instantiation metadata. This spec is a placeholder awaiting rewrite from Gherkin
DSL to standard describe/it syntax. The feature enables tracking which generic
types and functions have been instantiated during compilation.

## Syntax

```simple
# note.sdn records generic instantiations
# e.g., List<Int> instantiated at line 42
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Test Structure

### SMF note.sdn Instantiation Tracking

- ✅ tracks generic instantiation metadata

