# Mixin and Static Polymorphism Integration

> Mixins and static polymorphism complement each other:

<details>
<summary>Full Scenario Manual</summary>

# Mixin and Static Polymorphism Integration

Mixins and static polymorphism complement each other:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/language/mixin_static_poly_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Mixins and static polymorphism complement each other:
- **Mixins** provide horizontal composition (adding capabilities)
- **Static polymorphism** provides efficient abstraction (zero-cost dispatch)
- Together they enable flexible, performant designs

## Use Cases

### 1. Mixin with Trait Implementation

Mixins can provide trait implementations that use static dispatch:

```simple
trait Logger:
    fn log(msg: text)

mixin FileLogger:
    var log_path: text

impl Logger for FileLogger:
    fn log(msg: text):
        # Write to file

class Service:
    use FileLogger
    var name: text

use std.spec.step

fn process<T: Logger>(svc: T):
    bind static T  # Static dispatch to mixin's impl
    svc.log("Processing")
```

### 2. Generic Mixin with Static Dispatch

Generic mixins benefit from monomorphization:

```simple
trait Serializable:
    fn serialize() -> text

mixin Cached<T: Serializable>:
    var cache: T

    fn get_cached() -> text:
        bind static T
        return self.cache.serialize()
```

### 3. Multiple Mixins with Different Traits

Compose multiple capabilities with static dispatch:

```simple
trait Drawable:
    fn draw()

trait Updatable:
    fn update(dt: f32)

mixin Visual:
    var color: u32

impl Drawable for Visual:
    fn draw():
        print(f"Drawing with color {self.color}")

mixin Physics:
    var velocity: f32

impl Updatable for Physics:
    fn update(dt: f32):
        self.velocity += dt

class GameObject:
    use Visual
    use Physics
    var name: text

fn render<T: Drawable>(obj: T):
    bind static T
    obj.draw()

fn tick<T: Updatable>(obj: T, dt: f32):
    bind static T
    obj.update(dt)
```

## Benefits

1. **Zero-cost composition**: Mixins add no runtime overhead with static dispatch
2. **Type safety**: Full compile-time checking of trait implementations
3. **Code reuse**: Share implementations across types via mixins
4. **Performance**: Inlining and specialization optimize each use case
5. **Flexibility**: Mix and match traits and mixins as needed

## Best Practices

- Use `bind static` for known concrete types with mixin traits
- Default to dynamic dispatch when type flexibility is needed
- Combine mixins for orthogonal concerns (logging, caching, etc.)
- Let the compiler specialize generic mixin code per type

## Scenarios

### Integration - Mixin Trait Implementation

### Integration - Static Dispatch to Mixin

### Integration - Generic Mixin Static Dispatch

### Integration - Multiple Mixins Multiple Traits

### Integration - Mixin Trait Bounds

### Integration - Type Inference Mixed Features

### Integration - Performance Characteristics

### Integration - Error Handling


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b7ea5f8724acd7799ed7b47fdb8e7b48d2f0cba1a89552a0e2860c5fc767d4f7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7ea5f8724acd7799ed7b47fdb8e7b48d2f0cba1a89552a0e2860c5fc767d4f7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7ea5f8724acd7799ed7b47fdb8e7b48d2f0cba1a89552a0e2860c5fc767d4f7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/std/language/mixin_static_poly_integration_spec.spl
mirror: doc/06_spec/01_unit/lib/std/language/mixin_static_poly_integration_spec.md (current)
findings: 4 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/01_unit/lib/std/language/mixin_static_poly_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/language/mixin_static_poly_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/language/mixin_static_poly_integration_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/std/language/mixin_static_poly_integration_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
