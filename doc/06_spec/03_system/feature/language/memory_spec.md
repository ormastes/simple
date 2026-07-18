# Simple Language Memory and Ownership - Test Specification

> This file contains executable test cases extracted from memory.md. The original specification file remains as architectural reference documentation.

<!-- sdn-diagram:id=memory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=memory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

memory_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=memory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Memory and Ownership - Test Specification

This file contains executable test cases extracted from memory.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Reference |
| Type | Extracted Examples (Category B) |
| Reference | memory.md |
| Source | `test/03_system/feature/language/memory_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This file contains executable test cases extracted from memory.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/06_spec/feature/language/memory_spec.md

## Extracted Test Cases

17 test cases extracted covering:
- Value semantics (stack allocation, copy on assign)
- Reference semantics (heap allocation, shared ownership)
- Option types (present/absent values without null)
- Move semantics and ownership transfer
- Borrow rules (immutable borrows coexist; mutable borrow is exclusive)
- Lifetime tracking for safe resource cleanup

## Syntax

Value type — copied on assignment:

    struct Point:
        x: i64
        y: i64

    val a = Point(x: 1, y: 2)
    val b = a      # independent copy; mutating b does not affect a

Reference type — shared by default:

    class Buffer:
        var data: [u8]
        me push(b: u8): self.data = self.data.push(b)

    val r1 = Buffer.new()
    val r2 = r1    # same heap object; r2.push() visible through r1

Option type — no null pointers:

    val found: Option<i64> = Some(42)
    val empty: Option<i64> = None

    val value = found.unwrap_or(0)   # => 42
    empty.is_some()                  # => false

## Examples

    val opt = OptionI64.new(42)
    opt.is_some()    # => true
    opt.value()      # => 42

    val none = OptionI64.none()
    none.is_some()   # => false
    none.value_or(0) # => 0

## Key Concepts

**Value semantics** — assignment copies the data. Two variables are fully
independent after assignment. Mutations to one do not affect the other.

**Reference semantics** — class instances are heap-allocated. Assignment
copies the reference, not the data. Multiple variables can observe the same
mutation.

**Move semantics** — when ownership of a resource transfers, the source
variable becomes invalid. The compiler enforces this statically.

**Borrow rules** — a value can have many immutable borrows (`&T`) or exactly
one mutable borrow (`&mut T`) active at a time, never both simultaneously.

**Option<T>** — the type-safe null substitute. `None` instead of `null`;
`Some(v)` wraps a present value. Unwrapping a `None` is a compile-time error
unless the fallback path is handled.

**Region-based GC** — the GC layer is opt-in; by default, the compiler uses
reference counting with cycle detection for class types that escape to the
heap. `NoGC` regions enable deterministic cleanup for embedded code.

## Common Patterns

Safe optional chaining (no null checks):

    val user: Option<User> = find_user(id)
    val name = user.map(|u| u.name).unwrap_or("anonymous")

Early return on absent value:

    fn get_age(id: i64) -> Option<i64>:
        val user = find_user(id)?   # None propagates automatically
        Some(user.age)

Resource cleanup with `defer`:

    fn process_file(path: text) -> Result<text, text>:
        val f = open(path)?
        defer f.close()
        Ok(f.read_all())

## Scenarios

### Memory Spec

#### reference_and_pointer_kinds_1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reference = ReferenceBox.new(10)
expect(reference.read()).to_equal(10)
```

</details>

#### reference_and_pointer_kinds_2

1. var unique = UniqueBox new
   - Expected: unique.is_moved() is false
   - Expected: unique.take() equals `20`
   - Expected: unique.is_moved() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var unique = UniqueBox.new(20)
expect(unique.is_moved()).to_equal(false)
expect(unique.take()).to_equal(20)
expect(unique.is_moved()).to_equal(true)
```

</details>

#### reference_and_pointer_kinds_3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shared = SharedBox.new(30)
val cloned = shared.clone_box()
expect(shared.read()).to_equal(30)
expect(cloned.read()).to_equal(30)
expect(cloned.ref_count).to_equal(2)
```

</details>

#### reference_and_pointer_kinds_4

1. var weak = WeakBox new
   - Expected: weak.upgrade().is_some() is true
2. weak invalidate
   - Expected: weak.upgrade().is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var weak = WeakBox.new(40)
expect(weak.upgrade().is_some()).to_equal(true)
weak.invalidate()
expect(weak.upgrade().is_none()).to_equal(true)
```

</details>

#### reference_and_pointer_kinds_5

1. var pool = HandlePool new
   - Expected: pool.is_valid(handle) is true
   - Expected: pool.get(handle).unwrap_or(-1) equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = HandlePool.new()
val handle = pool.allocate(50)
expect(pool.is_valid(handle)).to_equal(true)
expect(pool.get(handle).unwrap_or(-1)).to_equal(50)
```

</details>

#### allocation_forms_new_variants_6

1. var unique = UniqueBox new
   - Expected: unique.take() equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var unique = UniqueBox.new(60)
expect(unique.take()).to_equal(60)
```

</details>

#### allocation_forms_new_variants_7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shared = SharedBox.new(70)
expect(shared.read()).to_equal(70)
expect(shared.clone_box().ref_count).to_equal(2)
```

</details>

#### allocation_forms_new_variants_8

1. var weak = WeakBox new
   - Expected: weak.upgrade().unwrap_or(-1) equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var weak = WeakBox.new(80)
expect(weak.upgrade().unwrap_or(-1)).to_equal(80)
```

</details>

#### allocation_forms_new_variants_9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val optional = OptionI64.some(90)
expect(optional.is_some()).to_equal(true)
expect(optional.unwrap_or(0)).to_equal(90)
```

</details>

#### allocation_forms_new_variants_10

1. var pool = HandlePool new
   - Expected: box.read().unwrap_or(-1) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = HandlePool.new()
val box = HandleBox.new(pool, 100)
expect(box.read().unwrap_or(-1)).to_equal(100)
```

</details>

#### global_handle_pools_11

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = HandlePool.new()
expect(pool.next_id).to_equal(0)
```

</details>

#### global_handle_pools_12

1. var pool = HandlePool new
   - Expected: pool.is_valid(h1) is true
   - Expected: pool.is_valid(h2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = HandlePool.new()
val h1 = pool.allocate(110)
val h2 = pool.allocate(120)
expect(pool.is_valid(h1)).to_equal(true)
expect(pool.is_valid(h2)).to_equal(true)
```

</details>

#### global_handle_pools_13

1. var pool = HandlePool new
   - Expected: pool.get(handle).unwrap_or(-1) equals `130`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = HandlePool.new()
val handle = pool.allocate(130)
expect(pool.get(handle).unwrap_or(-1)).to_equal(130)
```

</details>

#### global_handle_pools_14

1. var pool = HandlePool new
2. pool free
   - Expected: pool.is_valid(handle) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = HandlePool.new()
val handle = pool.allocate(140)
pool.free(handle)
expect(pool.is_valid(handle)).to_equal(false)
```

</details>

#### borrowing_15

1. var session = BorrowSession new
2. session borrow
   - Expected: session.can_write() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = BorrowSession.new(true)
session.borrow()
expect(session.can_write()).to_equal(true)
```

</details>

#### example_game_entity_system_with_handles_16

1. var world = World new
   - Expected: first equals `0`
   - Expected: second equals `1`
   - Expected: world.entity_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = World.new()
val first = world.spawn_entity(5)
val second = world.spawn_entity(8)
expect(first).to_equal(0)
expect(second).to_equal(1)
expect(world.entity_count()).to_equal(2)
```

</details>

#### note_on_option_types_17

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val none_value = OptionI64.none()
expect(none_value.is_none()).to_equal(true)
expect(none_value.unwrap_or(17)).to_equal(17)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
