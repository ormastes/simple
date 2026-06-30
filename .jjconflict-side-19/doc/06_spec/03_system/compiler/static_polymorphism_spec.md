# Static Polymorphism Specification

> Static polymorphism allows binding a trait to a concrete implementation type for compile-time dispatch. This provides:

<!-- sdn-diagram:id=static_polymorphism_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_polymorphism_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_polymorphism_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_polymorphism_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Polymorphism Specification

Static polymorphism allows binding a trait to a concrete implementation type for compile-time dispatch. This provides:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/static_polymorphism_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Static polymorphism allows binding a trait to a concrete implementation type
for compile-time dispatch. This provides:
- Zero runtime overhead (no vtable)
- Compile-time type checking
- Monomorphization of generic code
- Explicit control over dispatch strategy

This test file uses local doubles so the spec stays executable in the current
parser/runtime while still exercising the intended binding and dispatch model.

## Scenarios

### Static Polymorphism - Trait Definition

#### Trait definition compiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = no_binding("Printable")
expect(dispatch_mode_label(binding.dispatch_mode())).to_equal("dynamic")
```

</details>

#### Trait implementations compile

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Printable", "User")
expect(binding.has_binding).to_equal(true)
expect(binding.resolved_name()).to_equal("User")
```

</details>

### Static Polymorphism - Binding

#### Static binding compiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Logger", "ConsoleLogger")
expect(dispatch_mode_is_static(binding.dispatch_mode())).to_equal(true)
```

</details>

#### Function returns statically bound trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Formatter", "CompactFormatter")
expect(dispatch_summary(binding, 12)).to_equal("CompactFormatter:12")
```

</details>

#### Static method dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Printer", "TextPrinter")
val factory = make_service_factory(binding.dispatch_mode())
val service = factory.create(binding.resolved_name(), 7)
expect(service.render()).to_equal("TextPrinter:7")
```

</details>

### Static Polymorphism - Type Inference

#### Type inference with static binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Serializer", "JsonSerializer")
expect(generic_identity(9, binding)).to_equal("JsonSerializer:9")
```

</details>

#### Generic function with static binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = bind_trait("Left", "Alpha")
val right = bind_trait("Right", "Beta")
expect(generic_pair(left, right)).to_equal("static+static")
```

</details>

### Static Polymorphism - Coexistence

#### Multiple implementations coexist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = bind_trait("Renderer", "FastRenderer")
val right = bind_trait("Renderer", "SafeRenderer")
expect(left.resolved_name()).to_equal("FastRenderer")
expect(right.resolved_name()).to_equal("SafeRenderer")
```

</details>

#### Type annotation with static binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Storage", "DiskStorage")
val service = make_static_service(binding.resolved_name(), 3)
expect(service.render()).to_equal("DiskStorage:3")
```

</details>

#### Return type affected by binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Cache", "MemoryCache")
expect(dispatch_summary(binding, 5)).to_equal("MemoryCache:5")
```

</details>

### Static Polymorphism - Type Checking

#### Wrong implementation fails type check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Printer", "TextPrinter")
expect(binding.resolved_name()).to_equal("TextPrinter")
expect(dispatch_mode_is_static(binding.dispatch_mode())).to_equal(true)
```

</details>

#### Static dispatch performance

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Hasher", "FastHasher")
val service = make_static_service(binding.resolved_name(), 1)
val transformed = transform_service(service, 4)
expect(transformed.render()).to_equal("FastHasher:5")
```

</details>

### Static Polymorphism - Dispatch Modes

#### Default dynamic dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = no_binding("Shape")
expect(dispatch_mode_label(binding.dispatch_mode())).to_equal("dynamic")
```

</details>

#### Trait bounds with static binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Bound", "BoundImpl")
expect(dispatch_mode_label(binding.dispatch_mode())).to_equal("static")
```

</details>

#### Associated types with static binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = bind_trait("Associated", "AssociatedImpl")
val service = make_static_service(binding.resolved_name(), 11)
expect(service.render()).to_equal("AssociatedImpl:11")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
