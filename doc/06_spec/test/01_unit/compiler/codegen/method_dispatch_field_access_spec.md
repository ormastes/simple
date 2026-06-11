# Method Dispatch Field Access Specification

> 1. var container: FieldInitContainer = FieldInitContainer new

<!-- sdn-diagram:id=method_dispatch_field_access_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=method_dispatch_field_access_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

method_dispatch_field_access_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=method_dispatch_field_access_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Method Dispatch Field Access Specification

## Scenarios

### method dispatch — field-access / index / tuple receiver

#### field-access receiver (`container.widget.init()`)

#### dispatches through the struct field's declared type

1. var container: FieldInitContainer = FieldInitContainer new
2. container widget init
   - Expected: container.widget.last == 701 is true
   - Expected: container.other.tag == 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `container.widget` has `receiver.ty == FieldInitA` only when
# the field-type recovery path walks into the struct's field
# table. If that path is missing, the call mis-dispatches to
# `FieldInitB.init` and `last` stays at 0 (or `tag` flips).
var container: FieldInitContainer = FieldInitContainer.new()
container.widget.init()
expect(container.widget.last == 701).to_equal(true)
expect(container.other.tag == 0).to_equal(true)
```

</details>

#### index-access receiver (`arr[i].init()`)

#### dispatches through the array element type

1. var arr: [FieldInitA; 2] = [FieldInitA new
2. arr[0] init
   - Expected: arr[0].last == 701 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [FieldInitA; 2] = [FieldInitA.new(), FieldInitA.new()]
arr[0].init()
expect(arr[0].last == 701).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/method_dispatch_field_access_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- method dispatch — field-access / index / tuple receiver

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
