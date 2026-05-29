# Codegen Parity Completion Specification
*Source:* `test/feature/app/codegen_parity_completion_spec.spl`

## Overview




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

## Behavior

### Constants

## Constant Values

    Compile-time constant literals: integer, float, boolean.

- integer constant
- float constant cast to int
- boolean true
- boolean false

### Core Arithmetic

## Binary Arithmetic Operations

    Addition, subtraction, multiplication, division, modulo.

- addition
- subtraction
- multiplication
- division
- modulo
- nested arithmetic
- copy operation

### Comparison Operations

## Relational Operators

    All six comparison operators: ==, !=, <, <=, >, >=.

- equal - true
- equal - false
- not equal - true
- not equal - false
- less than - true
- less than - false
- less than or equal - equal
- less than or equal - false
- greater than - true
- greater than - false
- greater than or equal - equal
- greater than or equal - false

### Logical Operations

## Boolean Operators

    Short-circuit and, or, and bitwise xor.

- logical and - true
- logical and - false
- logical or - true
- logical or - false
- bitwise xor

### Unary Operations

## Unary Operators

    Negation and logical not.

- negation
- logical not

### Cast Operations

## Type Casting

    Integer to float and float to integer conversions.

- int to float to int roundtrip
- float truncation

### Control Flow

## Branching and Loops

    If-else, while, for, break, continue.

- if-else true branch
- if-else false branch
- nested if-else
- while loop accumulation
- while with break
- while with continue
- for range exclusive
- for range inclusive
- if expression without else
- while that does not execute

### Memory Operations

## Variable Assignment and Mutation

    Mutable variables, variable shadowing, scope cleanup.

- mutable variable assignment
- variable shadowing
- scope cleanup

### Struct and Field Operations

## Struct Initialization and Field Access

    Construction, field get, nested structs.

- struct init and field access
- nested struct
- deeply nested field access

### Collection Operations

## Arrays, Dicts, Tuples

    Literal construction, indexing, element types.

- array literal and indexing
- empty array
- array with float elements
- array with bool elements
- dict literal
- tuple literal and indexing
- tuple with float element
- tuple with bool element
- negative array index

### String Operations

## String Literals and Interpolation

    Const strings, interpolation with different types.

- const string
- string interpolation with int
- string interpolation with float
- string as non-boxed value

### Function Calls

## Function Definitions, Calls, Recursion

    Simple calls, multi-arg, recursion, implicit return.

- simple function call
- function with parameters
- recursive function
- multiple functions with locals
- implicit return
- nested function call

### Closures

## Lambda Expressions and Captures

    Lambdas without captures, closures with captures.

- lambda no capture
- closure with capture

### Method Calls

## Builtin and User-Defined Methods

    String length, array push, mutable methods.

- string length
- array push
- mutable struct method
- chained array operations

### Enum Operations

## Enum Variants

    Unit variants, payload variants, multiple variants.

- enum unit variant
- enum with payload
- multiple enum variants

### Pattern Matching

## Match Expressions

    Literal, binding, wildcard, enum, boolean, nested patterns.

- literal pattern
- binding pattern
- wildcard pattern
- bool pattern
- nested pattern matching

### Pointer Operations

## Reference and Dereference

    Pointer creation and dereference.

- pointer new and deref

### Boxing and Unboxing

## Value Boxing

    Int, float, bool boxing for collections and generic contexts.

- box unbox int
- float in array
- index set with float value
- index set with bool value

### Option and Result

## Option/Result Construction and Matching

    Some, None, Ok, Err.

- option some
- option none
- result ok
- result err

### Contract Operations

## Assertions

    Assert true passes, assert false would fail.

- assert true passes

### Generators

## Generator Yield

    Basic generator with yield and collection.

### Bitwise Operations

## Bitwise Operators

    And, or, xor, shift left, shift right.

- bitwise xor
- shift left
- shift right

### Float Arithmetic

## Floating-Point Operations

    Basic float math with cast to verify.

- float addition
- float multiplication

### For Loop Over Collection

## Collection Iteration

    For-in with array, not just range.

- for over array

### Compound Boolean Expressions

## Complex Boolean Logic

    Nested and/or, short-circuit evaluation.

- compound and-or
- nested and

### Multiple Return Paths

## Early Returns

    Functions with multiple return statements.

- early return from branch
- return with no value

### Expression Statement

## Non-Returned Expressions

    Expression evaluated for side effects, result discarded.

- expression statement ignored

### Print with Types

## Print Builtin

    Print with bool and float arguments (boxing paths).

- print bool
- print float

### GC and Memory

## Garbage Collection

    Large struct allocation triggers GC paths.

- gc alloc large struct

### Aggregate Operations

## Aggregate Construction

    Array, tuple, struct, and enum aggregate kinds for full MIR Aggregate coverage.

- array aggregate
- tuple aggregate
- struct aggregate field init
- enum with data aggregate

### Stack Allocation

## Alloc Instruction

    Mutable local allocation on stack.

- mutable local rewrite
- multiple mutable locals
- mutable struct field update

### Bitwise Not

## BitNot Unary Operator

    Bitwise complement operator.

- bitwise not zero
- bitwise not negative one

### Float Comparison

## Float Comparison Operators

    Eq, ne, lt, le, gt, ge on floats.

- float equal
- float not equal
- float less than
- float greater than

### Nop and Expression Discard

## Nop Instruction

    Statements that produce no-ops in MIR.

- standalone expression discard
- void call discard

### Move and Copy

## Move Instruction

    Move semantics for non-copyable types (strings, arrays).

- string move
- array move
- struct move

### Unsigned Arithmetic

## Unsigned Division and Remainder

    These exercise the udiv/urem codegen paths.

- unsigned modulo
- integer remainder

### Type Conversion

## Various Cast Paths

    Exercises different type conversion FFI paths in codegen.

- i64 to f64 and back
- bool to int
- negative int to float

### Const Zero

## Zero/Default Constant

    Zero-initialized values for various types.

- zero int
- zero float
- false bool

### Nil Literal

## Nil Value

    The nil/null literal expression.

- nil value
- nil in conditional

### Assume Statement

## Runtime Assumptions

    Assume statements declare runtime preconditions.

- assume true
- assume with expression

### Admit Statement

## Admit (Proof Skip)

    Admit is a no-op at runtime, used for proof obligations.

- admit true

### Global Variable

## Global Variable Load

    Access to module-level global constants.

- global constant access
- global in expression

### Loop Statement

## Infinite Loop

    Loop with explicit break, distinct from while.

- loop with break
- loop with early return

### References

## Pointer Ref

    Reference creation with &.

- reference creation

### Contract Expressions

## Function Contracts

    Ensures and requires clauses on functions.

- ensures postcondition
- requires precondition

### Bitwise Not

## Bitwise Complement

    The ~ operator for bitwise negation.

- bitnot zero
- bitnot identity

### If Expression

## If as Value

    If-else used as expression returning a value.

- if expression in binding
- nested if expression
- if expression in call argument

### Future and Await

## Async Operations

    Future creation and await expressions.

- future create and await
- future with expression

### Generator and Yield

## Generator Operations

    Generator creation with yield expressions.

- generator create and yield
- generator multiple yields

### Actor Spawn

## Actor Operations

    Spawning actor processes.

- actor spawn

### Contract Old

ensures: result == old(x) + 1

- contract old in postcondition

### GPU Intrinsic

## GPU Operations

    GPU intrinsic function calls.

- gpu intrinsic

### Neighbor Access

## GPU Stencil Neighbor

    Neighbor access for GPU stencil computations.

- neighbor access

### Proof Hint

## Proof Hint Statement

    Proof hints are no-ops at runtime, used for verification.

- proof hint statement
- proof hint with expression context

### Calc Block

## Calc Statement

    Calc blocks are verification constructs, no-ops at runtime.

- calc statement

### Vec Literal

## Vec Literal Expression

    Vec literals for growable array construction.

- vec literal


