# Perf Sugar Specification

> <details>

<!-- sdn-diagram:id=perf_sugar_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=perf_sugar_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

perf_sugar_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=perf_sugar_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Perf Sugar Specification

## Scenarios

### perf_sugar typed array allocation

#### f64 zeros creates correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = TypedBuffer.zeros(8)
expect(buf.size()).to_equal(8)
```

</details>

#### f64 zeros fills with zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = TypedBuffer.zeros(4)
expect(buf.get(0)).to_equal(0.0)
expect(buf.get(3)).to_equal(0.0)
```

</details>

#### f64 fill creates uniform buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = TypedBuffer.fill(5, 3.14)
expect(buf.size()).to_equal(5)
expect(buf.get(0)).to_equal(3.14)
expect(buf.get(4)).to_equal(3.14)
```

</details>

#### int zeros creates correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = IntBuffer.zeros(6)
expect(buf.size()).to_equal(6)
expect(buf.get(0)).to_equal(0)
expect(buf.get(5)).to_equal(0)
```

</details>

#### byte alloc via rt_bytes_alloc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = ByteBuffer.alloc(16)
expect(buf.size()).to_equal(16)
```

</details>

#### empty buffer has zero length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = TypedBuffer.zeros(0)
expect(buf.size()).to_equal(0)
```

</details>

#### single element buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = TypedBuffer.fill(1, 42.0)
expect(buf.size()).to_equal(1)
expect(buf.get(0)).to_equal(42.0)
```

</details>

#### int buffer preserves values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = IntBuffer.zeros(3)
expect(buf.get(0)).to_equal(0)
expect(buf.get(1)).to_equal(0)
expect(buf.get(2)).to_equal(0)
```

</details>

#### moderate size allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = TypedBuffer.zeros(100)
expect(buf.size()).to_equal(100)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/perf_sugar_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- perf_sugar typed array allocation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
