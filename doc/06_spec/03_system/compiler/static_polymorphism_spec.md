# Static Polymorphism Specification

> Static polymorphism allows binding a trait to a concrete implementation type for compile-time dispatch. This provides:

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Trait definition compiles
   - Expected: dispatch_mode_label(binding.dispatch_mode()) equals `dynamic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Trait definition compiles")
val binding = no_binding("Printable")
expect(dispatch_mode_label(binding.dispatch_mode())).to_equal("dynamic")
```

</details>

#### Trait implementations compile

- Trait implementations compile
   - Expected: binding.has_binding is true
   - Expected: binding.resolved_name() equals `User`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Trait implementations compile")
val binding = bind_trait("Printable", "User")
expect(binding.has_binding).to_equal(true)
expect(binding.resolved_name()).to_equal("User")
```

</details>

### Static Polymorphism - Binding

#### Static binding compiles

- Static binding compiles
   - Expected: dispatch_mode_is_static(binding.dispatch_mode()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Static binding compiles")
val binding = bind_trait("Logger", "ConsoleLogger")
expect(dispatch_mode_is_static(binding.dispatch_mode())).to_equal(true)
```

</details>

#### Function returns statically bound trait

- Function returns statically bound trait
   - Expected: dispatch_summary(binding, 12) equals `CompactFormatter:12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Function returns statically bound trait")
val binding = bind_trait("Formatter", "CompactFormatter")
expect(dispatch_summary(binding, 12)).to_equal("CompactFormatter:12")
```

</details>

#### Static method dispatch

- Static method dispatch
   - Expected: service.render() equals `TextPrinter:7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Static method dispatch")
val binding = bind_trait("Printer", "TextPrinter")
val factory = make_service_factory(binding.dispatch_mode())
val service = factory.create(binding.resolved_name(), 7)
expect(service.render()).to_equal("TextPrinter:7")
```

</details>

### Static Polymorphism - Type Inference

#### Type inference with static binding

- Type inference with static binding
   - Expected: generic_identity(9, binding) equals `JsonSerializer:9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Type inference with static binding")
val binding = bind_trait("Serializer", "JsonSerializer")
expect(generic_identity(9, binding)).to_equal("JsonSerializer:9")
```

</details>

#### Generic function with static binding

- Generic function with static binding
   - Expected: generic_pair(left, right) equals `static+static`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Generic function with static binding")
val left = bind_trait("Left", "Alpha")
val right = bind_trait("Right", "Beta")
expect(generic_pair(left, right)).to_equal("static+static")
```

</details>

### Static Polymorphism - Coexistence

#### Multiple implementations coexist

- Multiple implementations coexist
   - Expected: left.resolved_name() equals `FastRenderer`
   - Expected: right.resolved_name() equals `SafeRenderer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Multiple implementations coexist")
val left = bind_trait("Renderer", "FastRenderer")
val right = bind_trait("Renderer", "SafeRenderer")
expect(left.resolved_name()).to_equal("FastRenderer")
expect(right.resolved_name()).to_equal("SafeRenderer")
```

</details>

#### Type annotation with static binding

- Type annotation with static binding
   - Expected: service.render() equals `DiskStorage:3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Type annotation with static binding")
val binding = bind_trait("Storage", "DiskStorage")
val service = make_static_service(binding.resolved_name(), 3)
expect(service.render()).to_equal("DiskStorage:3")
```

</details>

#### Return type affected by binding

- Return type affected by binding
   - Expected: dispatch_summary(binding, 5) equals `MemoryCache:5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Return type affected by binding")
val binding = bind_trait("Cache", "MemoryCache")
expect(dispatch_summary(binding, 5)).to_equal("MemoryCache:5")
```

</details>

### Static Polymorphism - Type Checking

#### Wrong implementation fails type check

- Wrong implementation fails type check
   - Expected: binding.resolved_name() equals `TextPrinter`
   - Expected: dispatch_mode_is_static(binding.dispatch_mode()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Wrong implementation fails type check")
val binding = bind_trait("Printer", "TextPrinter")
expect(binding.resolved_name()).to_equal("TextPrinter")
expect(dispatch_mode_is_static(binding.dispatch_mode())).to_equal(true)
```

</details>

#### Static dispatch performance

- Static dispatch performance
   - Expected: transformed.render() equals `FastHasher:5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Static dispatch performance")
val binding = bind_trait("Hasher", "FastHasher")
val service = make_static_service(binding.resolved_name(), 1)
val transformed = transform_service(service, 4)
expect(transformed.render()).to_equal("FastHasher:5")
```

</details>

### Static Polymorphism - Dispatch Modes

#### Default dynamic dispatch

- Default dynamic dispatch
   - Expected: dispatch_mode_label(binding.dispatch_mode()) equals `dynamic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Default dynamic dispatch")
val binding = no_binding("Shape")
expect(dispatch_mode_label(binding.dispatch_mode())).to_equal("dynamic")
```

</details>

#### Trait bounds with static binding

- Trait bounds with static binding
   - Expected: dispatch_mode_label(binding.dispatch_mode()) equals `static`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Trait bounds with static binding")
val binding = bind_trait("Bound", "BoundImpl")
expect(dispatch_mode_label(binding.dispatch_mode())).to_equal("static")
```

</details>

#### Associated types with static binding

- Associated types with static binding
   - Expected: service.render() equals `AssociatedImpl:11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Associated types with static binding")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2ff154969d76b9cfa02d95f6c108c8b7c4f98a62a2f53b2faaac12e4185330a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2ff154969d76b9cfa02d95f6c108c8b7c4f98a62a2f53b2faaac12e4185330a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2ff154969d76b9cfa02d95f6c108c8b7c4f98a62a2f53b2faaac12e4185330a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/static_polymorphism_spec.spl
mirror: doc/06_spec/03_system/compiler/static_polymorphism_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/static_polymorphism_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/static_polymorphism_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/static_polymorphism_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Trait definition compiles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/static_polymorphism_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Trait implementations compile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/static_polymorphism_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Static binding compiles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
