# Effect System (Async/Sync Inference)

*Source: `simple/std_lib/test/features/infrastructure/effect_system_spec.spl`*

---

# Effect System (Async/Sync Inference)

**Feature ID:** #101
**Category:** Infrastructure - Type System
**Difficulty:** 4/5
**Status:** Complete

## Overview

The Effect System automatically infers whether functions are synchronous or asynchronous
based on their implementation, implementing Simple's async-by-default concurrency model.

## Key Features

- **Automatic Effect Inference:** No manual async/await annotations required
- **Suspension Detection:** Identifies await, if~, while~, for~ operators
- **Effect Propagation:** Calling async functions makes caller async
- **Promise Wrapping:** Auto-wraps return types in Promise<T>
- **Sync Constraints:** Validates sync annotated functions

## Implementation

**Primary Files:**
- `src/type/src/effects.rs` - Effect inference algorithm

**Verification:**
- `verification/type_inference_compile/src/AsyncEffectInference.lean` - Lean 4 proofs

**Dependencies:**
- Feature #2: Parser
- Feature #100: Type Inference

**Required By:**
- Feature #4: HIR
- Feature #107: Interpreter

**Given** pure computation function
        **When** effect inference runs
        **Then** infers Sync effect

        **Verification:** Pure function is sync

**Given** function with sync keyword
        **When** effect inference runs
        **Then** enforces Sync constraint

        **Verification:** Sync annotation respected

**Given** function containing await
        **When** effect inference runs
        **Then** infers Async effect

        **Verification:** Await makes function async

**Given** function calling async function
        **When** effect inference runs
        **Then** infers Async for caller

        **Verification:** Effect propagation works

**Given** sync-annotated function
        **When** validation runs
        **Then** ensures no suspension points

        **Verification:** Sync constraint enforced
