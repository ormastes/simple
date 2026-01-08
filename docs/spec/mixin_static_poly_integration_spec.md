# Mixin and Static Polymorphism Integration

*Source: `./simple/std_lib/test/unit/language/mixin_static_poly_integration_spec.spl`*

---

# Mixin and Static Polymorphism Integration

This specification covers the interaction between mixins and static polymorphism,
demonstrating how these features work together for efficient, type-safe code composition.

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
    fn log(self, msg: String)

mixin FileLogger:
    var log_path: String
    
impl Logger for FileLogger:
    fn log(self, msg: String):
        # Write to file

class Service:
    use FileLogger
    var name: String

fn process<T: Logger>(svc: T):
    bind static T  # Static dispatch to mixin's impl
    svc.log("Processing")
```

### 2. Generic Mixin with Static Dispatch

Generic mixins benefit from monomorphization:

```simple
trait Serializable:
    fn serialize(self) -> String

mixin Cached<T: Serializable>:
    var cache: T
    
    fn get_cached(self) -> String:
        bind static T
        return self.cache.serialize()
```

### 3. Multiple Mixins with Different Traits

Compose multiple capabilities with static dispatch:

```simple
trait Drawable:
    fn draw(self)
    
trait Updatable:
    fn update(self, dt: f32)

mixin Visual:
    var color: u32
    
impl Drawable for Visual:
    fn draw(self):
        print(f"Drawing with color {self.color}")

mixin Physics:
    var velocity: f32
    
impl Updatable for Physics:
    fn update(self, dt: f32):
        self.velocity += dt

class GameObject:
    use Visual
    use Physics
    var name: String

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

Test that mixins can implement traits

Test static dispatch to trait implemented by mixin

Test generic mixin methods with static dispatch

Test class with multiple mixins implementing different traits

Test generic mixin with trait bounds on parameters

Test type inference with both mixins and static polymorphism

Test that integration has no additional overhead

Test error messages for invalid mixin/trait combinations
