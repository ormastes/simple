# Call-Site Argument Labels

> Call-site labels are postfix keywords attached to arguments at the call site that improve readability of function calls by making the role of each argument explicit. Labels such as `to`, `from`, `by`, `into`, `onto`, and `with` are declared on parameter definitions and optionally used at the call site. Labels are purely syntactic sugar for documentation purposes -- the argument is still matched by position, and omitting the label is valid. This spec validates all six built-in labels, label-free calling, and multi-label combinations.

<!-- sdn-diagram:id=call_site_label_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=call_site_label_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

call_site_label_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=call_site_label_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Call-Site Argument Labels

Call-site labels are postfix keywords attached to arguments at the call site that improve readability of function calls by making the role of each argument explicit. Labels such as `to`, `from`, `by`, `into`, `onto`, and `with` are declared on parameter definitions and optionally used at the call site. Labels are purely syntactic sugar for documentation purposes -- the argument is still matched by position, and omitting the label is valid. This spec validates all six built-in labels, label-free calling, and multi-label combinations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-012 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/call_site_label_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Call-site labels are postfix keywords attached to arguments at the call site that improve
readability of function calls by making the role of each argument explicit. Labels such
as `to`, `from`, `by`, `into`, `onto`, and `with` are declared on parameter definitions
and optionally used at the call site. Labels are purely syntactic sugar for documentation
purposes -- the argument is still matched by position, and omitting the label is valid.
This spec validates all six built-in labels, label-free calling, and multi-label
combinations.

## Syntax

```simple
fn copy_item(src to, dst):
dst
val result = copy_item("a" to, "b")

fn scale(value, factor by):
value * factor
val result = scale(10, 3 by)

fn transfer(amount, src from, dst to):
amount
val result = transfer(100, "checking" from, "savings" to)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Call-Site Label | A postfix keyword (`to`, `from`, `by`, `into`, `onto`, `with`) on an argument |
| Parameter Label | Declared in the function signature after the parameter name |
| Optional Usage | Labels can be omitted at the call site; arguments match by position |
| Multiple Labels | A single function can use different labels on different parameters |

## Scenarios

### Call-site labels

#### basic label usage

#### allows to label

1. fn copy item


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn copy_item(src to, dst):
    dst
val result = copy_item("a" to, "b")
expect result == "b"
```

</details>

#### allows from label

1. fn fetch


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn fetch(url, origin from):
    origin
val result = fetch("http://example.com", "localhost" from)
expect result == "localhost"
```

</details>

#### allows by label

1. fn scale


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn scale(value, factor by):
    value * factor
val result = scale(10, 3 by)
expect result == 30
```

</details>

#### allows into label

1. fn convert


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn convert(data, fmt into):
    fmt
val result = convert("raw", "json" into)
expect result == "json"
```

</details>

#### allows onto label

1. fn place


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn place(item, target onto):
    target
val result = place("widget", "canvas" onto)
expect result == "canvas"
```

</details>

#### allows with label

1. fn open file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn open_file(path, mode with):
    mode
val result = open_file("/tmp/f", "rw" with)
expect result == "rw"
```

</details>

#### no label cases

#### works without labels

1. fn add


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    a + b
val result = add(3, 4)
expect result == 7
```

</details>

#### works with label on param but no label on arg

1. fn copy item2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn copy_item2(src to, dst):
    dst
val result = copy_item2("a", "b")
expect result == "b"
```

</details>

#### multiple labels

#### supports from and to labels together

1. fn transfer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn transfer(amount, src from, dst to):
    amount
val result = transfer(100, "checking" from, "savings" to)
expect result == 100
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
