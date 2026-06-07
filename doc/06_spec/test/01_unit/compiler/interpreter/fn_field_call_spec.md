# Fn Field Call Specification

> <details>

<!-- sdn-diagram:id=fn_field_call_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fn_field_call_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fn_field_call_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fn_field_call_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fn Field Call Specification

## Scenarios

### interpreter function-typed field calls

#### calls a function extracted from an object field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = FnFieldRoute(handler: plus_one)
val h = route.handler
expect(h(41)).to_equal(42)
```

</details>

#### calls a function stored in an object field with method-call syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = FnFieldRoute(handler: plus_one)
expect(route.handler(41)).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/fn_field_call_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- interpreter function-typed field calls

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
