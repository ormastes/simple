# Simple Language Memory and Ownership - Test Specification

This file contains executable test cases extracted from memory.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Status | Reference |
| Type | Extracted Examples (Category B) |
| Reference | memory.md |
| Source | `test/specs/memory_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

This file contains executable test cases extracted from memory.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/06_spec/memory.md

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/memory/summary.txt` |

## Scenarios

- reference_and_pointer_kinds_1
- reference_and_pointer_kinds_2
- reference_and_pointer_kinds_3
- reference_and_pointer_kinds_4
- reference_and_pointer_kinds_5
- allocation_forms_new_variants_6
- allocation_forms_new_variants_7
- allocation_forms_new_variants_8
- allocation_forms_new_variants_9
- allocation_forms_new_variants_10
- global_handle_pools_11
- global_handle_pools_12
- global_handle_pools_13
- global_handle_pools_14
- borrowing_15
- example_game_entity_system_with_handles_16
- note_on_option_types_17
