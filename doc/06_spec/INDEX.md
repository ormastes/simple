# Test Specification Index

*Generated: 2026-03-30 00:09:40*

## Quick Stats

- **Total Features:** 13
- **Complete Documentation:** 13 (100%)
- **Stubs Remaining:** 0
- **Total Lines:** 408
- **Warnings:** 24

---

## Other (11 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Async-Default Function Model](async_default.md) | Draft | Thin | N/A | 16 | This document specifies Simple's async-default execution model where functions are async by default and sync is explici… |
| [Capability-Based Effects Specification](capability_effects.md) | Planned | Thin | N/A | 14 | Capability-based effect system that prevents LLMs from silently adding I/O or stateful behavior to pure code. Explicit… |
| [Macro Specification](macro.md) | SPECIFICATION (Partially Implemented) | Thin | N/A | 1 | This file contains executable test cases extracted from macro.md. The original specification file remains as architectu… |
| [Module System Specification - Test Specification](modules.md) | Reference | Thin | N/A | 1 | This file contains executable test cases extracted from modules.md. The original specification file remains as architec… |
| [Simple Language Concurrency - Test Specification](concurrency.md) | Reference | Thin | N/A | 24 | This file contains executable test cases extracted from concurrency.md. The original specification file remains as arch… |
| [Simple Language Data Structures - Test Specification](data_structures.md) | Reference | Thin | N/A | 32 | This file contains executable test cases extracted from data_structures.md. The original specification file remains as… |
| [Simple Language Functions and Pattern Matching - Test Specification](functions.md) | Reference | Needs detail | N/A | 22 | This file contains executable test cases extracted from functions.md. The original specification file remains as archit… |
| [Simple Language Memory and Ownership - Test Specification](memory.md) | Reference | Thin | N/A | 17 | This file contains executable test cases extracted from memory.md. The original specification file remains as architect… |
| [Simple Language Traits and Implementations - Test Specification](traits.md) | Implemented (uses existing coherence rules) | Thin | N/A | 36 | This file contains executable test cases extracted from traits.md. The original specification file remains as architect… |
| [Suspension Operator (`~`) Specification](suspension_operator.md) | Draft | Thin | N/A | 24 | The `~` operator marks expressions that may suspend (perform async operations). It appears in three contexts: |
| [Type Inference Specification - Test Specification](type_inference.md) | Partial Implementation (Hindley-Milner scaffold working) | Thin | N/A | 16 | Simple uses a Hindley-Milner-style type inference system that automatically deduces types for expressions, variables, a… |

## Tooling (2 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Remote Baremetal Library Checks](remote_baremetal_library_spec.md) | Implemented | Thin | 3/5 | 22 | Checks the library surface that should remain usable for the `interpreter(remote(baremetal(riscv32)))` and `interpreter… |
| [Remote Baremetal Runtime Checks](remote_baremetal_runtime_spec.md) | Implemented | Thin | 3/5 | 16 | Checks the current remote baremetal execution plumbing used by the Simple test runner. The spec covers: |

## Residual Files

These files are present in `doc/06_spec` but were not regenerated in this run.

| File | Type |
|------|------|
| bootstrap_test_gate.sdn | Data/config artifact |
| feature.md | Legacy markdown |
| feature_db.sdn | Data/config artifact |
| metaprogramming.md | Legacy markdown |
| pending_feature.md | Legacy markdown |
| sandboxing.md | Legacy markdown |
| shell_api.md | Legacy markdown |
| syntax.md | Legacy markdown |
| tensor_dimensions.md | Legacy markdown |
| types.md | Legacy markdown |

