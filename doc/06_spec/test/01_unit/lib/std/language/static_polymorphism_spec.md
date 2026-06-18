# Static Polymorphism Feature Specification

> trait Drawable:

<!-- sdn-diagram:id=static_polymorphism_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_polymorphism_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_polymorphism_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_polymorphism_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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
