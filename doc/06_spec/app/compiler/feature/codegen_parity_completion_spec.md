# Codegen Parity Completion Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/codegen_parity_completion_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 160 |
| Active scenarios | 160 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/app/codegen_parity_completion/result.json` |

## Scenarios

- integer constant
- float constant cast to int
- boolean true
- boolean false
- addition
- subtraction
- multiplication
- division
- modulo
- nested arithmetic
- copy operation
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
- logical and - true
- logical and - false
- logical or - true
- logical or - false
- bitwise xor
- negation
- logical not
- int to float to int roundtrip
- float truncation
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
- mutable variable assignment
- variable shadowing
- scope cleanup
- struct init and field access
- nested struct
- deeply nested field access
- array literal and indexing
- empty array
- array with float elements
- array with bool elements
- dict literal
- tuple literal and indexing
- tuple with float element
- tuple with bool element
- negative array index
- const string
- string interpolation with int
- string interpolation with float
- string as non-boxed value
- simple function call
- function with parameters
- recursive function
- multiple functions with locals
- implicit return
- nested function call
- lambda no capture
- closure with capture
- string length
- array push
- mutable struct method
- chained array operations
- enum unit variant
- enum with payload
- multiple enum variants
- literal pattern
- binding pattern
- wildcard pattern
- bool pattern
- nested pattern matching
- pointer new and deref
- box unbox int
- float in array
- index set with float value
- index set with bool value
- option some
- option none
- result ok
- result err
- assert true passes
- bitwise xor
- shift left
- shift right
- float addition
- float multiplication
- for over array
- compound and-or
- nested and
- early return from branch
- return with no value
- expression statement ignored
- print bool
- print float
- gc alloc large struct
- array aggregate
- tuple aggregate
- struct aggregate field init
- enum with data aggregate
- mutable local rewrite
- multiple mutable locals
- mutable struct field update
- bitwise not zero
- bitwise not negative one
- float equal
- float not equal
- float less than
- float greater than
- standalone expression discard
- void call discard
- string move
- array move
- struct move
- unsigned modulo
- integer remainder
- i64 to f64 and back
- bool to int
- negative int to float
- zero int
- zero float
- false bool
- nil value
- nil in conditional
- assume true
- assume with expression
- admit true
- global constant access
- global in expression
- loop with break
- loop with early return
- reference creation
- ensures postcondition
- requires precondition
- bitnot zero
- bitnot identity
- if expression in binding
- nested if expression
- if expression in call argument
- future create and await
- future with expression
- generator create and yield
- generator multiple yields
- actor spawn
- contract old in postcondition
- gpu intrinsic
- neighbor access
- proof hint statement
- proof hint with expression context
- calc statement
- vec literal
