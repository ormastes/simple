# Simple Language Functions and Pattern Matching - Test Specification

This file contains executable test cases extracted from functions.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Status | Reference |
| Type | Extracted Examples (Category B) |
| Reference | functions.md |
| Source | `/home/ormastes/dev/pub/simple/test/specs/functions_spec.spl` |
| Updated | 2026-03-29 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

This file contains executable test cases extracted from functions.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/06_spec/functions.md

## Extracted Test Cases

24 test cases extracted covering:
- Core functionality examples
- Edge cases and validation
- Integration patterns

Functions in Simple are defined with the `fn` keyword. The syntax is inspired by Python's definition...

Functions have an inferred async/sync effect based on their body:

Simple supports first-class functions - you can assign functions to variables or pass them as argume...

An inline lambda uses a backslash to introduce parameters (inspired by ML-family languages):

The backslash syntax was chosen for one-pass parsing - seeing `\` immediately signals a lambda, requ...

Lambdas capture variables from their enclosing scope:

Methods can accept trailing blocks for iteration or DSL constructs:

Pattern matching is a powerful feature enabling branching on the structure of data. The `match` expr...

fn describe_token(tok: Token) -> String:
    match tok:
        case Number(val):
            return...

```simple
match x:
    case 0:
        print "Zero"
    case 1:
        print "One"
```

```simple
match x:
    case 1 | 2 | 3:
        print "Small number"
```

```simple
match x:
    case n if n < 0:
        print "Negative number: {n}"
    case n if n > 100:
...

```simple
match x:
    case 0:
        print "Zero"
    case _:
        print "Non-zero"
```

val p = Point(x: 5, y: 0)
match p:
    case Point(x: 0, y: 0):
        print "Origin"
    case Point...

All possibilities must be covered (exhaustive matching), otherwise the code will not compile:

The `Constructor<T>` type represents any constructor that produces an instance of `T` or a subtype:

```simple
# Constructor<T> - type for constructors producing T or subtypes
val factory: Constructor[...

1. Must accept all required parameters of parent constructor
2. Additional parameters must have defa...

| Parent Constructor | Child Constructor | Valid? | Reason |
|-------------------|------------------...

val factory = get_widget_factory("button")
val w = factory("Dynamic Button")
```

Specify exact constructor signatures:

Constructor polymorphism enables clean dependency injection:

Use traits to define abstract constructor requirements:

Public functions should use semantic types (unit types, enums, Option) instead of bare primitives. S...

## Scenarios

- functions_2
- functions_3
- lambdas_and_closures_4
- lambdas_and_closures_5
- lambdas_and_closures_6
- lambdas_and_closures_7
- pattern_matching_8
- pattern_matching_9
- pattern_matching_10
- pattern_matching_11
- pattern_matching_12
- pattern_matching_13
- pattern_matching_14
- pattern_matching_15
- constructor_polymorphism_16
- constructor_polymorphism_17
- constructor_polymorphism_18
- constructor_polymorphism_19
- constructor_polymorphism_20
- constructor_polymorphism_22
- constructor_polymorphism_23
- semantic_types_in_function_signatures_24
