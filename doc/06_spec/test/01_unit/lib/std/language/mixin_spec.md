# Mixin Feature Specification

> mixin MixinName<T>:

<!-- sdn-diagram:id=mixin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mixin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mixin_spec -> MixinName<ConcreteType>
mixin_spec -> Timestamp
mixin_spec -> Logger<text>
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mixin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# Mixin Feature Specification

mixin MixinName<T>:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/language/mixin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Features

- **Field composition**: Add fields from mixins to classes
- **Method composition**: Add methods from mixins to classes
- **Generic mixins**: Parameterize mixins with type variables
- **Multiple mixins**: Apply multiple mixins to a single class
- **Type safety**: Full type checking and inference for mixin usage

## Syntax

```simple
mixin MixinName<T>:
    field_name: Type

    fn method_name(param: T) -> ReturnType:
        # implementation

class ClassName:
    use MixinName<ConcreteType>
    # class body
```

## Examples

Basic mixin with timestamp fields:

```simple
mixin Timestamp:
    var created_at: i64
    var updated_at: i64

class User:
    use Timestamp
    var name: text
```

Generic mixin for logging:

```simple
mixin Logger<T>:
    var log_level: i32

    fn log(message: T):
        print(message)

class Service:
    use Logger<text>
```

Multiple mixins composition:

```simple
class Document:
    use Timestamp
    use Logger<text>
    var content: text
```

## Scenarios

### Mixin - Basic Declaration

### Mixin - Method Declaration

### Mixin - Generic Parameters

### Mixin - Class Application

### Mixin - Multiple Composition

### Mixin - Type Inference

### Mixin - Name Conflicts

### Mixin - Generic Substitution


</details>
