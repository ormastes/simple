# Arc Specification

> <details>

<!-- sdn-diagram:id=arc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arc_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arc Specification

## Scenarios

### Arc Type Syntax

#### @T type annotation

#### parses @T as atomic pointer type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser test: val x: @Data
expect true
```

</details>

#### parses @T with generic parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser test: val x: @List<Int>
expect true
```

</details>

#### parses nested @T types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser test: val x: @Option<@Data>
expect true
```

</details>

#### Arc allocation (new@)

#### allocates with new@ syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val shared: @Data = new@ Data(42)
expect true
```

</details>

#### has initial refcount of 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# arc.strong_count() == 1
expect true
```

</details>

#### Arc cloning

#### atomically increments refcount on clone

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val arc2 = arc1.clone()
expect true
```

</details>

#### shares data between clones

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# arc1.borrow() == arc2.borrow()
expect true
```

</details>

#### Arc thread safety

#### can be sent across threads

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# spawn { process(arc.clone()) }
expect true
```

</details>

#### maintains correct count across threads

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Concurrent clone/drop
expect true
```

</details>

#### Arc weak references

#### creates weak reference from Arc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val weak = arc.downgrade()
expect true
```

</details>

#### upgrades weak to Arc atomically

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# weak.upgrade() returns Option<Value>
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/arc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Arc Type Syntax

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
