# Simple Language Data Structures - Test Specification

This file contains executable test cases extracted from data_structures.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Status | Executable coverage |
| Type | Extracted Examples (Category B) |
| Reference | data_structures.md |
| Source | `test/specs/data_structures_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

This file contains executable test cases extracted from data_structures.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/06_spec/data_structures.md

## Extracted Test Cases

32 test cases extracted covering:
- Struct value types (stack-allocated, copyable)
- Class reference types (heap-allocated, shared references)
- Auto-forwarding properties with get/set/is accessors
- Enums and algebraic data types (ADTs)
- Strong enums (ordered, next/prev, labelable)
- Union types, Option, and Result types
- Bit-field registers and visibility modifiers

## Syntax

Value type (struct — copied on assignment):

    struct Vector2:
        x: i64
        y: i64

    val p = Vector2.new(2, 3)
    p.manhattan()  # => 5

Reference type (class — shared by default):

    class Counter:
        var count: i64
        me inc(): self.count = self.count + 1

Enum (algebraic data type):

    enum Color:
        Red
        Green
        Blue

Option and Result:

    val maybe: Option<i64> = Some(42)
    val ok: Result<i64, text> = Ok(10)
    val err: Result<i64, text> = Err("oops")

## Examples

    val p = Vector2.new(2, 3)
    p.manhattan()          # => 5

    val c = Counter.new(1)
    val alias = c
    alias.inc()
    c.current()            # => 2  (shared reference)

    val sep = Counter.new(1)
    sep.inc()
    sep.current()          # => 2  (independent)

    val v = TextOrNumber.Text("hello")
    v.describe()           # => "text:hello"

    val light = TrafficLight.Amber
    light.next().label()   # => "green"

## Key Concepts

**Struct vs Class** — structs are value types (copied on assignment, stack
preferred); classes are reference types (heap-allocated, shared by default).
Choose struct for small, pure-data records; class for mutable shared state.

**Auto-forwarding properties** — the `get`/`set`/`is` prefix convention
lets the compiler auto-generate accessor methods from field declarations.

**Strong enums** — enums with a defined total order and a `next()`/`prev()`
cycle. Useful for state machines, traffic lights, ring buffers.

**Union types** — `text | i64` (or named ADT variants) let a single value
hold one of several types. Pattern matching is exhaustive.

**Option<T>** — the canonical null-safe wrapper. `Some(v)` or `None`.
All accesses through `unwrap_or`, `map`, `and_then` — no null dereferences.

**Result<T, E>** — either `Ok(v)` or `Err(e)`. The `?` operator propagates
errors automatically in functions returning `Result`.

**Bit-field registers** — fixed-width integer fields with named bit ranges,
useful for hardware register modelling and protocol parsing.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/data_structures/summary.txt` |

## Scenarios

- structs_value_types_1
- structs_value_types_2
- classes_reference_types_3
- classes_reference_types_4
- classes_reference_types_5
- auto_forwarding_properties_getsetis_6
- auto_forwarding_properties_getsetis_7
- auto_forwarding_properties_getsetis_8
- enums_algebraic_data_types_9
- enums_algebraic_data_types_10
- enums_algebraic_data_types_11
- enums_algebraic_data_types_12
- strong_enums_13
- strong_enums_14
- strong_enums_15
- union_types_16
- option_type_17
- option_type_18
- visibility_and_access_19
- result_type_20
- result_type_21
- result_type_22
- result_type_23
- bitfields_24
- bitfields_25
- bitfields_26
- bitfields_27
- bitfields_28
- bitfields_29
- bitfields_30
- bitfields_31
- bitfields_32
