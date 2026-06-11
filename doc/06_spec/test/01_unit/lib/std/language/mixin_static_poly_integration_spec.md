# Mixin and Static Polymorphism Integration

> Mixins and static polymorphism complement each other:

<!-- sdn-diagram:id=mixin_static_poly_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mixin_static_poly_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mixin_static_poly_integration_spec -> FileLogger
mixin_static_poly_integration_spec -> Visual
mixin_static_poly_integration_spec -> Physics
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mixin_static_poly_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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
