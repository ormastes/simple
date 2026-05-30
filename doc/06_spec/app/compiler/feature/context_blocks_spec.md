# Scoped Context Blocks for Resource Management

**Feature ID:** #LANG-040 | **Category:** Language | **Status:** In Progress

_Source: `test/feature/usage/context_blocks_spec.spl`_

---

## Overview

Context blocks provide scoped execution environments that guarantee setup and teardown
semantics, similar to Python's `with` statement or RAII in C++. They enable safe resource
management by ensuring cleanup code runs regardless of how the block exits. This spec
validates basic context execution, nested context support, variable scoping within
contexts, and proper cleanup guarantees when exceptions occur.

## Syntax

```simple
context "Basic context execution":
    it "executes code within context scope":
        skip

context "Nested contexts":
    it "supports properly nested context blocks":
        skip

context "Context variables":
    it "maintains context-scoped variables":
        skip
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Context block | A scoped execution region with guaranteed setup/teardown |
| Setup/teardown | Code that runs before and after the context body executes |
| Nested contexts | Contexts within contexts, with proper ordering of cleanup |
| Context variables | Variables whose lifetime is bound to the enclosing context scope |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 8 |

## Test Structure

### Context Blocks

#### Basic context execution

- ✅ executes code within context scope
#### Setup and teardown

- ✅ runs setup before and teardown after context
#### Nested contexts

- ✅ supports properly nested context blocks
#### Exception handling in contexts

- ✅ ensures cleanup even when exceptions occur
#### Context variables

- ✅ maintains context-scoped variables

