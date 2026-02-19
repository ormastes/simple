# Codegen Parity Completion Specification

**Feature ID:** #CODEGEN-PARITY-001 | **Category:** Compilation | **Status:** In Progress

_Source: `test/feature/app/codegen_parity_completion_spec.spl`_

---

## Overview

Tests for code generation parity across backends (Interpreter, Cranelift JIT, LLVM).
Each test exercises a specific MIR instruction category and verifies consistent
results regardless of backend.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Backend Parity | Same source produces same result on all backends |
| MIR Category | Group of related MIR instructions (constants, binops, control flow, etc.) |
| Instruction Coverage | Each test targets specific MIR instruction(s) |

## Behavior

- Every MIR instruction category is exercised at least once
- Tests use only i64 returns for deterministic comparison
- Tests are grouped by MIR category matching the Rust integration tests

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 160 |

## Test Structure

### Constants

- ✅ integer constant
- ✅ float constant cast to int
- ✅ boolean true
- ✅ boolean false
### Core Arithmetic

- ✅ addition
- ✅ subtraction
- ✅ multiplication
- ✅ division
- ✅ modulo
- ✅ nested arithmetic
- ✅ copy operation
### Comparison Operations

- ✅ equal - true
- ✅ equal - false
- ✅ not equal - true
- ✅ not equal - false
- ✅ less than - true
- ✅ less than - false
- ✅ less than or equal - equal
- ✅ less than or equal - false
- ✅ greater than - true
- ✅ greater than - false
- ✅ greater than or equal - equal
- ✅ greater than or equal - false
### Logical Operations

- ✅ logical and - true
- ✅ logical and - false
- ✅ logical or - true
- ✅ logical or - false
- ✅ bitwise xor
### Unary Operations

- ✅ negation
- ✅ logical not
### Cast Operations

- ✅ int to float to int roundtrip
- ✅ float truncation
### Control Flow

- ✅ if-else true branch
- ✅ if-else false branch
- ✅ nested if-else
- ✅ while loop accumulation
- ✅ while with break
- ✅ while with continue
- ✅ for range exclusive
- ✅ for range inclusive
- ✅ if expression without else
- ✅ while that does not execute
### Memory Operations

- ✅ mutable variable assignment
- ✅ variable shadowing
- ✅ scope cleanup
### Struct and Field Operations

- ✅ struct init and field access
- ✅ nested struct
- ✅ deeply nested field access
### Collection Operations

- ✅ array literal and indexing
- ✅ empty array
- ✅ array with float elements
- ✅ array with bool elements
- ✅ dict literal
- ✅ tuple literal and indexing
- ✅ tuple with float element
- ✅ tuple with bool element
- ✅ negative array index
### String Operations

- ✅ const string
- ✅ string interpolation with int
- ✅ string interpolation with float
- ✅ string as non-boxed value
### Function Calls

- ✅ simple function call
- ✅ function with parameters
- ✅ recursive function
- ✅ multiple functions with locals
- ✅ implicit return
- ✅ nested function call
### Closures

- ✅ lambda no capture
- ✅ closure with capture
### Method Calls

- ✅ string length
- ✅ array push
- ✅ mutable struct method
- ✅ chained array operations
### Enum Operations

- ✅ enum unit variant
- ✅ enum with payload
- ✅ multiple enum variants
### Pattern Matching

- ✅ literal pattern
- ✅ binding pattern
- ✅ wildcard pattern
- ✅ bool pattern
- ✅ nested pattern matching
### Pointer Operations

- ✅ pointer new and deref
### Boxing and Unboxing

- ✅ box unbox int
- ✅ float in array
- ✅ index set with float value
- ✅ index set with bool value
### Option and Result

- ✅ option some
- ✅ option none
- ✅ result ok
- ✅ result err
### Contract Operations

- ✅ assert true passes
### Generators

### Bitwise Operations

- ✅ bitwise xor
- ✅ shift left
- ✅ shift right
### Float Arithmetic

- ✅ float addition
- ✅ float multiplication
### For Loop Over Collection

- ✅ for over array
### Compound Boolean Expressions

- ✅ compound and-or
- ✅ nested and
### Multiple Return Paths

- ✅ early return from branch
- ✅ return with no value
### Expression Statement

- ✅ expression statement ignored
### Print with Types

- ✅ print bool
- ✅ print float
### GC and Memory

- ✅ gc alloc large struct
### Aggregate Operations

- ✅ array aggregate
- ✅ tuple aggregate
- ✅ struct aggregate field init
- ✅ enum with data aggregate
### Stack Allocation

- ✅ mutable local rewrite
- ✅ multiple mutable locals
- ✅ mutable struct field update
### Bitwise Not

- ✅ bitwise not zero
- ✅ bitwise not negative one
### Float Comparison

- ✅ float equal
- ✅ float not equal
- ✅ float less than
- ✅ float greater than
### Nop and Expression Discard

- ✅ standalone expression discard
- ✅ void call discard
### Move and Copy

- ✅ string move
- ✅ array move
- ✅ struct move
### Unsigned Arithmetic

- ✅ unsigned modulo
- ✅ integer remainder
### Type Conversion

- ✅ i64 to f64 and back
- ✅ bool to int
- ✅ negative int to float
### Const Zero

- ✅ zero int
- ✅ zero float
- ✅ false bool
### Nil Literal

- ✅ nil value
- ✅ nil in conditional
### Assume Statement

- ✅ assume true
- ✅ assume with expression
### Admit Statement

- ✅ admit true
### Global Variable

- ✅ global constant access
- ✅ global in expression
### Loop Statement

- ✅ loop with break
- ✅ loop with early return
### References

- ✅ reference creation
### Contract Expressions

- ✅ ensures postcondition
- ✅ requires precondition
### Bitwise Not

- ✅ bitnot zero
- ✅ bitnot identity
### If Expression

- ✅ if expression in binding
- ✅ nested if expression
- ✅ if expression in call argument
### Future and Await

- ✅ future create and await
- ✅ future with expression
### Generator and Yield

- ✅ generator create and yield
- ✅ generator multiple yields
### Actor Spawn

- ✅ actor spawn
### Contract Old

- ✅ contract old in postcondition
### GPU Intrinsic

- ✅ gpu intrinsic
### Neighbor Access

- ✅ neighbor access
### Proof Hint

- ✅ proof hint statement
- ✅ proof hint with expression context
### Calc Block

- ✅ calc statement
### Vec Literal

- ✅ vec literal

