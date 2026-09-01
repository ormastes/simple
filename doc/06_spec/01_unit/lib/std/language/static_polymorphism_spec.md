# Static Polymorphism Feature Specification

> trait Drawable:

<details>
<summary>Full Scenario Manual</summary>

# Static Polymorphism Feature Specification

trait Drawable:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/language/static_polymorphism_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Features

- **Compile-time dispatch**: No vtable overhead, direct function calls
- **Monomorphization**: Generate specialized code for each concrete type
- **Type safety**: Full type checking at compile time
- **Trait bounds**: Specify required traits for generic parameters
- **Static binding**: Resolved at compile time with `bind static`

## Syntax

```simple
trait Drawable:
    fn draw()

struct Circle:
    radius: f32

impl Drawable for Circle:
    fn draw():
        print("Drawing circle")

use std.spec.step

fn render<T: Drawable>(shape: T):
    bind static T  # Static dispatch
    shape.draw()
```

## Performance

Static polymorphism provides:
- **Zero vtable overhead**: No runtime indirection
- **Inline optimization**: Functions can be inlined
- **Type specialization**: Optimized code for each type
- **No allocation**: Works with stack-only types

## Comparison with Dynamic Dispatch

| Feature | Static (`bind static`) | Dynamic (default) |
|---------|----------------------|-------------------|
| Dispatch | Compile-time | Runtime (vtable) |
| Overhead | Zero | Pointer indirection |
| Code size | Larger (duplication) | Smaller (shared) |
| Inlining | Yes | Limited |

## Examples

Basic static dispatch:

```simple
trait Printable:
    fn to_string() -> text

struct Point:
    x: i32
    y: i32

impl Printable for Point:
    fn to_string() -> text:
        return f"({self.x}, {self.y})"

fn display<T: Printable>(obj: T):
    bind static T
    print(obj.to_string())
```

Multiple trait bounds:

```simple
fn process<T: Printable + Comparable>(item: T):
    bind static T
    print(item.to_string())
    item.compare(item)
```

Generic struct with static dispatch:

```simple
struct Container<T: Drawable>:
    item: T

    fn render():
        bind static T
        self.item.draw()
```

## Scenarios

### Static Polymorphism - Basic Binding

### Static Polymorphism - Trait Bounds

### Static Polymorphism - Monomorphization

### Static Polymorphism - Multiple Traits

### Static Polymorphism - Generic Structs

### Static Polymorphism - Type Inference

### Static Polymorphism - Error Detection

### Static Polymorphism - Performance


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c6201af7350a9bbb8ef2813b6fc8b3e95abcf66d490c7ec44bc2358886ef85a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c6201af7350a9bbb8ef2813b6fc8b3e95abcf66d490c7ec44bc2358886ef85a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c6201af7350a9bbb8ef2813b6fc8b3e95abcf66d490c7ec44bc2358886ef85a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/std/language/static_polymorphism_spec.spl
mirror: doc/06_spec/01_unit/lib/std/language/static_polymorphism_spec.md (current)
findings: 4 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/01_unit/lib/std/language/static_polymorphism_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/language/static_polymorphism_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/language/static_polymorphism_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/std/language/static_polymorphism_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
