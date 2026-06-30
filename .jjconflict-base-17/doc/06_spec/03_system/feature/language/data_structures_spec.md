# Simple Language Data Structures - Test Specification

> This file contains executable test cases extracted from data_structures.md. The original specification file remains as architectural reference documentation.

<!-- sdn-diagram:id=data_structures_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=data_structures_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

data_structures_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=data_structures_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Data Structures - Test Specification

This file contains executable test cases extracted from data_structures.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Executable coverage |
| Type | Extracted Examples (Category B) |
| Reference | data_structures.md |
| Source | `test/03_system/feature/language/data_structures_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This file contains executable test cases extracted from data_structures.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/06_spec/feature/language/data_structures_spec.md

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

## Common Patterns

Newtype pattern (wrap a primitive to add type safety):

    struct Meters:
        value: i64
        fn add(other: Meters) -> Meters:
            Meters(value: self.value + other.value)

Builder pattern (return `self` from mutating methods):

    val config = Config.new().with_width(80).with_height(24)

## Scenarios

### Data Structures Spec

#### structs_value_types_1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Vector2.new(2, 3)
expect(same_vector(p, Vector2.new(2, 3))).to_equal(true)
expect(p.manhattan()).to_equal(5)
```

</details>

#### structs_value_types_2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Vector2.new(4, 1)
expect(same_vector(p, Vector2.new(4, 1))).to_equal(true)
expect(p.manhattan()).to_equal(5)
```

</details>

#### classes_reference_types_3

1. left inc
   - Expected: left.current() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = Counter.new(1)
left.inc()
expect(left.current()).to_equal(2)
```

</details>

#### classes_reference_types_4

1. counter add
   - Expected: counter.current() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counter = Counter.new(10)
counter.add(5)
expect(counter.current()).to_equal(15)
```

</details>

#### classes_reference_types_5

1. right inc
   - Expected: left.current() equals `1`
   - Expected: right.current() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = Counter.new(1)
val right = Counter.new(1)
right.inc()
expect(left.current()).to_equal(1)
expect(right.current()).to_equal(2)
```

</details>

#### auto_forwarding_properties_getsetis_6

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = PropertyBox.new("alpha", true, "hidden")
expect(box.is_enabled()).to_equal(true)
expect(box.label()).to_equal("alpha:on")
```

</details>

#### auto_forwarding_properties_getsetis_7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = PropertyBox.new("beta", false, "hidden")
box.name = "gamma"
expect(box.label()).to_equal("gamma:off")
```

</details>

#### auto_forwarding_properties_getsetis_8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val box = PropertyBox.new("delta", true, "secret")
box.secret = "changed"
expect(box.secret).to_equal("changed")
```

</details>

#### enums_algebraic_data_types_9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = MaybeNumber.Some(9)
expect(value.is_some()).to_equal(true)
expect(value.unwrap_or(0)).to_equal(9)
```

</details>

#### enums_algebraic_data_types_10

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(describe_optional_number(MaybeNumber.Some(4))).to_equal("some:4")
expect(describe_optional_number(MaybeNumber.None)).to_equal("none")
```

</details>

#### enums_algebraic_data_types_11

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(describe_color(Color.Red)).to_equal("red")
expect(describe_color(Color.Green)).to_equal("green")
expect(describe_color(Color.Blue)).to_equal("blue")
```

</details>

#### enums_algebraic_data_types_12

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(describe_union(TextOrNumber.Text("hello"))).to_equal("text:hello")
expect(describe_union(TextOrNumber.Number(7))).to_equal("number:7")
```

</details>

#### strong_enums_13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(describe_light(TrafficLight.Red.next().next().next())).to_equal("red")
```

</details>

#### strong_enums_14

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start = TrafficLight.Green
expect(describe_light(start.next().next())).to_equal("amber")
```

</details>

#### strong_enums_15

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(describe_light(TrafficLight.Amber.next())).to_equal("green")
```

</details>

#### union_types_16

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(describe_union(TextOrNumber.Text("alpha"))).to_equal("text:alpha")
expect(describe_union(TextOrNumber.Number(11))).to_equal("number:11")
```

</details>

#### option_type_17

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val some = MaybeNumber.Some(42)
expect(some.is_some()).to_equal(true)
expect(some.unwrap_or(0)).to_equal(42)
```

</details>

#### option_type_18

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val none = MaybeNumber.None
expect(none.is_some()).to_equal(false)
expect(none.unwrap_or(17)).to_equal(17)
```

</details>

#### visibility_and_access_19

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = AccessBox.new(7, 5)
expect(record.expose()).to_equal(12)
expect(record.public_value).to_equal(7)
```

</details>

#### result_type_20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_checked(3, 4)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap_or(0)).to_equal(7)
```

</details>

#### result_type_21

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_checked(8, 9)
expect(describe_result(result)).to_equal("ok:17")
```

</details>

#### result_type_22

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = ResultValue.Ok(5)
val err = ResultValue.Err("broken")
expect(ok.message()).to_equal("ok:5")
expect(err.message()).to_equal("broken")
```

</details>

#### result_type_23

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe = MaybeNumber.Some(6)
val result = add_checked(maybe.unwrap_or(0), 1)
expect(result.unwrap_or(0)).to_equal(7)
```

</details>

#### bitfields_24

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val register = BitRegister.new(0)
expect(describe_register(register)).to_equal("raw:0")
```

</details>

#### bitfields_25

1. register set flag
   - Expected: register.has_flag(1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val register = BitRegister.new(0)
register.set_flag(1)
expect(register.has_flag(1)).to_equal(true)
```

</details>

#### bitfields_26

1. register write field
   - Expected: register.read_field(12, 2) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val register = BitRegister.new(0)
register.write_field(12, 2, 3)
expect(register.read_field(12, 2)).to_equal(3)
```

</details>

#### bitfields_27

1. register set flag
2. register clear flag
   - Expected: register.has_flag(4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val register = BitRegister.new(0)
register.set_flag(4)
register.clear_flag(4)
expect(register.has_flag(4)).to_equal(false)
```

</details>

#### bitfields_28

1. register write field
   - Expected: register.read_field(48, 4) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val register = BitRegister.new(0)
register.write_field(48, 4, 2)
expect(register.read_field(48, 4)).to_equal(2)
```

</details>

#### bitfields_29

1. register write field
   - Expected: is_wide_field(register.read_field(240, 4)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val register = BitRegister.new(0)
register.write_field(240, 4, 9)
expect(is_wide_field(register.read_field(240, 4))).to_equal(false)
```

</details>

#### bitfields_30

1. register write field
   - Expected: register.read_field(240, 4) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val register = BitRegister.new(0)
register.write_field(240, 4, 15)
expect(register.read_field(240, 4)).to_equal(15)
```

</details>

#### bitfields_31

1. register write field
   - Expected: register.read_field(15, 0) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val register = BitRegister.new(0)
register.write_field(15, 0, 7)
expect(register.read_field(15, 0)).to_equal(7)
```

</details>

#### bitfields_32

1. register write field
   - Expected: register.read_field(240, 4) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val register = BitRegister.new(0)
register.write_field(240, 4, 16)
expect(register.read_field(240, 4)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
