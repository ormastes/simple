# MIR

*Source: `simple/std_lib/test/features/infrastructure/mir_spec.spl`*

---

# MIR

**Feature ID:** #5
**Category:** Infrastructure
**Difficulty:** 4/5
**Status:** Complete

## Overview

Mid-level IR with 50+ instruction variants. Lowers HIR to basic blocks with explicit control flow. Handles arithmetic, memory, collections, patterns, async, and generators.

## Syntax

MIR provides low-level instructions for:
- **Core (6):** ConstInt, ConstFloat, BinOp, UnaryOp, Call, Return
- **Memory (6):** Load, Store, FieldGet, FieldSet, Alloc, Dealloc
- **Collections (7):** ArrayLit, TupleLit, DictLit, IndexGet, IndexSet, Slice, Len
- **Strings (3):** ConstString, FStringFormat, StringConcat
- **Patterns (6):** PatternTest, PatternBind, EnumDiscriminant, TupleDestruct, ArrayDestruct, WildcardPattern
- **Async (5):** FutureCreate, Await, PromiseResolve, PromiseReject, EffectSuspend
- **Generators (3):** GeneratorCreate, Yield, GeneratorNext

## Implementation

**Files:**
- `src/compiler/src/mir/mod.rs`
- `src/compiler/src/mir/instructions.rs`
- `src/compiler/src/mir/lower.rs`

**Test Files:**
- `src/driver/tests/runner_tests.rs`

**Dependencies:** #4 (HIR)
**Required By:** #100 (Codegen)

## Notes

MIR uses SSA form. Generator lowering creates state machines. Effect tracking for async safety.
