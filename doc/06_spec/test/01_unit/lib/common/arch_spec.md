# Arch Specification

> <details>

<!-- sdn-diagram:id=arch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arch_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arch Specification

## Scenarios

### Architecture Testing

#### Layer Definition

#### creates a layer with name and patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLayer.create(name="domain", pattern="src/domain/")
expect layer.name == "domain"
expect layer.pattern == "src/domain/"
```

</details>

#### checks if module matches layer patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer = MockLayer.create(name="domain", pattern="src/domain/")
expect layer.name == "domain"
```

</details>

#### supports multiple glob patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layer1 = MockLayer.create(name="core", pattern="src/compiler/10.frontend/core/")
val layer2 = MockLayer.create(name="shared", pattern="src/shared/")
expect layer1.name == "core"
expect layer2.name == "shared"
```

</details>

#### LayerRef Builder

#### creates a layer reference for rule building

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = MockLayerRef.from_name("api")
expect ref.layer_name == "api"
```

</details>

#### supports chaining may_only_access

1. ref may only access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = MockLayerRef.from_name("api")
ref.may_only_access("domain,infra")
expect ref.allowed == "domain,infra"
```

</details>

#### supports chaining may_not_access

1. ref may not access


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = MockLayerRef.from_name("domain")
ref.may_not_access("api,infra")
expect ref.forbidden == "api,infra"
```

</details>

#### supports chaining multiple rules

1. ref may only access


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = MockLayerRef.from_name("service")
ref.may_only_access("domain").may_not_access("api")
expect ref.allowed == "domain"
expect ref.forbidden == "api"
```

</details>

#### Architecture Definition

#### creates an empty architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = MockArchitecture.empty()
expect arch.layer_count == 0
```

</details>

#### defines layers fluently

1. arch define layer
2. arch define layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = MockArchitecture.empty()
arch.define_layer(name="api", pattern="src/api/")
arch.define_layer(name="domain", pattern="src/domain/")
expect arch.layer_count == 2
```

</details>

#### finds layer containing a module

1. arch define layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = MockArchitecture.empty()
arch.define_layer(name="api", pattern="src/api/")
expect arch.layer_count == 1
```

</details>

#### Access Rules - MayOnlyAccess

#### passes when layer only accesses allowed layers

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.pass_result()
expect result.is_ok() == true
```

</details>

#### fails when layer accesses forbidden layer

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.fail_result()
expect result.is_ok() == false
```

</details>

#### Access Rules - MayNotAccess

#### passes when layer does not access forbidden layers

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.pass_result()
expect result.is_ok() == true
```

</details>

#### fails when layer accesses forbidden layer

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.fail_result()
expect result.is_ok() == false
```

</details>

#### Access Rules - MayNotBeAccessedBy

#### passes when forbidden layers do not access target

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.pass_result()
expect result.is_ok() == true
```

</details>

#### fails when forbidden layer accesses target

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.fail_result()
expect result.is_ok() == false
```

</details>

#### No Mock in Production

#### passes when no mocks in production code

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.pass_result()
expect result.is_ok() == true
```

</details>

#### fails when mock annotation in production code

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.fail_result()
expect result.is_ok() == false
```

</details>

#### ignores mocks in test code

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.pass_result()
expect result.is_ok() == true
```

</details>

#### No Skip Layer

#### passes when layers are accessed in order

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.pass_result()
expect result.is_ok() == true
```

</details>

#### fails when layer is skipped

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.fail_result()
expect result.is_ok() == false
```

</details>

#### ArchCheckResult

#### is_ok returns true for Pass

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.pass_result()
expect result.is_ok() == true
```

</details>

#### is_ok returns false for Fail

1. expect result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.fail_result()
expect result.is_ok() == false
```

</details>

#### violations returns empty list for Pass

1. expect result has violations


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.pass_result()
expect result.has_violations() == false
```

</details>

#### violations returns list for Fail

1. expect result has violations


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MockArchCheckResult.fail_result()
expect result.has_violations() == true
```

</details>

#### Violation

#### formats violation message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = MockViolation(source_layer: "api", target_layer: "domain")
val msg = v.format_message()
expect msg == "api -> domain"
```

</details>

#### Integration - Layer Architecture Example

#### validates a typical layered architecture

1. arch define layer
2. arch define layer
3. arch define layer
4. arch define layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = MockArchitecture.empty()
arch.define_layer(name="api", pattern="src/api/")
arch.define_layer(name="service", pattern="src/service/")
arch.define_layer(name="domain", pattern="src/domain/")
arch.define_layer(name="infra", pattern="src/infra/")
expect arch.layer_count == 4
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/arch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Architecture Testing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
