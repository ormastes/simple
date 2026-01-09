# Simple Language Specifications - Index

**Generated:** 2026-01-09 06:15:42
**Total Specs:** 16
**Total Tests:** 292

## Quick Navigation

- [Advanced Features](#advanced-features) (3 specs)
- [Async/Concurrency](#asyncconcurrency) (3 specs)
- [Core Language](#core-language) (5 specs)
- [Data Structures](#data-structures) (1 specs)
- [Miscellaneous](#miscellaneous) (1 specs)
- [Testing & Quality](#testing-&-quality) (1 specs)
- [Type System](#type-system) (2 specs)

---

## Advanced Features {#advanced-features}

### [Capability-Based Effects Specification](capability_effects.md)
**Status:** 📋 Planned | **Tests:** 14 | **Feature IDs:** **Keywords:**

Capability-based effect system that prevents LLMs from silently adding I/O or stateful behavior to pure code. Explicit effect markers (`@pure`, `@io`,...


### [- Test Specification](macro.md)
**Status:** SPECIFICATION (Partially Implemented) | **Tests:** 0 | **Feature IDs:** **Source:** macro.md

This file contains executable test cases extracted from macro.md.


### [Simple Language Metaprogramming - Test Specification](metaprogramming.md)
**Status:** Reference | **Tests:** 24 | **Feature IDs:** **Source:** metaprogramming.md

This file contains executable test cases extracted from metaprogramming.md.


---

## Async/Concurrency {#asyncconcurrency}

### [Async-Default Function Model](async_default.md)
**Status:** Draft | **Tests:** 31 | **Feature IDs:** #276-285

This document specifies Simple's async-default execution model where functions are async by default and sync is explicit.


### [Simple Language Concurrency - Test Specification](concurrency.md)
**Status:** Reference | **Tests:** 24 | **Feature IDs:** **Source:** concurrency.md

This file contains executable test cases extracted from concurrency.md.


### [Suspension Operator (`~`) Specification](suspension_operator.md)
**Status:** Draft | **Tests:** 24 | **Feature IDs:** #270-275

The `~` operator marks expressions that may suspend (perform async operations). It appears in three contexts:


---

## Core Language {#core-language}

### [Simple Language Functions and Pattern Matching - Test Specification](functions.md)
**Status:** Reference | **Tests:** 24 | **Feature IDs:** **Source:** functions.md

This file contains executable test cases extracted from functions.md.


### [Simple Language Memory and Ownership - Test Specification](memory.md)
**Status:** Reference | **Tests:** 17 | **Feature IDs:** **Source:** memory.md

This file contains executable test cases extracted from memory.md.


### [Module System Specification - Test Specification](modules.md)
**Status:** Reference | **Tests:** 0 | **Feature IDs:** **Source:** modules.md

This file contains executable test cases extracted from modules.md.


### [Simple Language Syntax Specification](syntax.md)
**Status:** Stable | **Tests:** 21 | **Feature IDs:** #10-19

Comprehensive specification of Simple's syntax, execution modes, and lexical structure.


### [Simple Language Traits and Implementations - Test Specification](traits.md)
**Status:** ✅ Implemented (uses existing coherence rules) | **Tests:** 36 | **Feature IDs:** **Source:** traits.md

This file contains executable test cases extracted from traits.md.


---

## Data Structures {#data-structures}

### [Simple Language Data Structures - Test Specification](data_structures.md)
**Status:** Reference | **Tests:** 32 | **Feature IDs:** **Source:** data_structures.md

This file contains executable test cases extracted from data_structures.md.


---

## Miscellaneous {#miscellaneous}

### [Shell API Specification](shell_api.md)
**Status:** Implementing | **Tests:** 8 | **Feature IDs:** #900-905

Shell API provides access to system operations commonly used in shell scripts:


---

## Testing & Quality {#testing-&-quality}

### [Sandboxing & Isolation](sandboxing.md)
**Status:** ✅ Runtime Complete (#916-919), 📋 Environment Planned (#920-923) | **Tests:** 0 | **Feature IDs:** #916-923

### Two Isolation Models


---

## Type System {#type-system}

### [Type Inference Specification](type_inference.md)
**Status:** Partial Implementation (Hindley-Milner scaffold working) | **Tests:** 24 | **Feature IDs:** #13

Simple uses a Hindley-Milner-style type inference system that automatically deduces types for expressions, variables, and functions without requiring ...


### [Simple Language Type System](types.md)
**Status:** Stable | **Tests:** 13 | **Feature IDs:** #20-29

Complete specification of Simple's type system, including primitives, composites, generics, and mutability rules.


---

## Statistics

**By Status:**
- Draft: 2 specs
- Implementing: 1 specs
- Partial Implementation (Hindley-Milner scaffold working): 1 specs
- Reference: 6 specs
- SPECIFICATION (Partially Implemented): 1 specs
- Stable: 2 specs
- ✅ Implemented (uses existing coherence rules): 1 specs
- ✅ Runtime Complete (#916-919), 📋 Environment Planned (#920-923): 1 specs
- 📋 Planned: 1 specs

**By Test Count:**
- 30+ tests: 3 specs
- 20-29 tests: 6 specs
- 10-19 tests: 3 specs
- <10 tests: 4 specs

**Total Test Coverage:** 292 test cases
