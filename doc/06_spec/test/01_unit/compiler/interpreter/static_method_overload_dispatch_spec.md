# Static Method Overload Dispatch Specification

> <details>

<!-- sdn-diagram:id=static_method_overload_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_method_overload_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_method_overload_dispatch_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_method_overload_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Method Overload Dispatch Specification

## Scenarios

### interpreter static method overload dispatch

#### selects the inline static overload for i64 arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var value: i64 = 7
expect(InlineStaticOverload.select(value)).to_equal("inline-i64")
```

</details>

#### selects the inline static overload for text arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var value: text = "hello"
expect(InlineStaticOverload.select(value)).to_equal("inline-text")
```

</details>

#### selects the impl-defined static overload for i64 arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var value: i64 = 9
expect(ImplStaticOverload.select(value)).to_equal("impl-i64")
```

</details>

#### selects the impl-defined static overload for text arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var value: text = "world"
expect(ImplStaticOverload.select(value)).to_equal("impl-text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/static_method_overload_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- interpreter static method overload dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
