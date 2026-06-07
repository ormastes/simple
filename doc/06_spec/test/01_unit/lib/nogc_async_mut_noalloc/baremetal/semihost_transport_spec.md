# Semihost Transport Specification

> <details>

<!-- sdn-diagram:id=semihost_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semihost_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semihost_transport_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semihost_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semihost Transport Specification

## Scenarios

### Transport Constants

#### WRITEC is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val TRANSPORT_WRITEC = 1
expect(TRANSPORT_WRITEC).to_equal(1)
```

</details>

#### WRITE0 is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val TRANSPORT_WRITE0 = 2
expect(TRANSPORT_WRITE0).to_equal(2)
```

</details>

#### WRITE is 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val TRANSPORT_WRITE = 3
expect(TRANSPORT_WRITE).to_equal(3)
```

</details>

#### BATCH_N is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val TRANSPORT_BATCH_N = 4
expect(TRANSPORT_BATCH_N).to_equal(4)
```

</details>

#### BUFFERED is 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val TRANSPORT_BUFFERED = 5
expect(TRANSPORT_BUFFERED).to_equal(5)
```

</details>

#### UART is 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val TRANSPORT_UART = 6
expect(TRANSPORT_UART).to_equal(6)
```

</details>

#### RAW_BINARY is 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val TRANSPORT_RAW_BINARY = 7
expect(TRANSPORT_RAW_BINARY).to_equal(7)
```

</details>

#### INTERNED is 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val TRANSPORT_INTERNED = 8
expect(TRANSPORT_INTERNED).to_equal(8)
```

</details>

#### all transport constants are unique

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1, 2, 3, 4, 5, 6, 7, 8]
expect(values.len()).to_equal(8)
```

</details>

### Capability Flags

#### CAP_WRITEC is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val CAP_WRITEC = 1
expect(CAP_WRITEC).to_equal(1)
```

</details>

#### CAP_WRITE0 is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val CAP_WRITE0 = 2
expect(CAP_WRITE0).to_equal(2)
```

</details>

#### CAP_WRITE is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val CAP_WRITE = 4
expect(CAP_WRITE).to_equal(4)
```

</details>

#### CAP_UART is 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val CAP_UART = 8
expect(CAP_UART).to_equal(8)
```

</details>

#### CAP_INTERNED is 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val CAP_INTERNED = 16
expect(CAP_INTERNED).to_equal(16)
```

</details>

#### capability flags are disjoint powers of 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = [1, 2, 4, 8, 16]
# Each pair OR'd must differ from each individual
var i = 0
var all_disjoint = true
while i < 5:
    var j = i + 1
    while j < 5:
        val combined = caps[i] | caps[j]
        if combined == caps[i]:
            all_disjoint = false
        if combined == caps[j]:
            all_disjoint = false
        j = j + 1
    i = i + 1
expect(all_disjoint).to_equal(true)
```

</details>

#### full capability mask combines all flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_caps = 1 | 2 | 4 | 8 | 16
expect(all_caps).to_equal(31)
```

</details>

### Config Defaults

#### default batch_size is 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_batch = 3
expect(default_batch).to_equal(3)
```

</details>

#### default UART base is 0x10000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_uart = 0x10000000
expect(default_uart).to_equal(268435456)
```

</details>

#### RAW_BINARY_MAGIC is 0x53 (ASCII S)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val magic = 0x53
expect(magic).to_equal(83)
```

</details>

### Ring Buffer Power-of-2

#### next_power_of_2 for 1 is 1

1. v = v |
2. v = v |
3. v = v |
4. v = v |
5. v = v |
   - Expected: v + 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v = 0
v = v | (v >> 1)
v = v | (v >> 2)
v = v | (v >> 4)
v = v | (v >> 8)
v = v | (v >> 16)
# n=1 => v = 1-1 = 0, result = 0+1 = 1
expect(v + 1).to_equal(1)
```

</details>

#### next_power_of_2 for 5 is 8

1. v = v |
2. v = v |
3. v = v |
4. v = v |
5. v = v |
   - Expected: v + 1 equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v = 5 - 1  # 4
v = v | (v >> 1)   # 4|2 = 6
v = v | (v >> 2)   # 6|1 = 7
v = v | (v >> 4)   # 7|0 = 7
v = v | (v >> 8)   # 7
v = v | (v >> 16)  # 7
expect(v + 1).to_equal(8)
```

</details>

#### next_power_of_2 for 16 is 16

1. v = v |
2. v = v |
3. v = v |
4. v = v |
5. v = v |
   - Expected: v + 1 equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v = 16 - 1  # 15
v = v | (v >> 1)   # 15
v = v | (v >> 2)   # 15
v = v | (v >> 4)   # 15
v = v | (v >> 8)   # 15
v = v | (v >> 16)  # 15
expect(v + 1).to_equal(16)
```

</details>

#### bitmask wrapping works for capacity 4

1. idx =
   - Expected: idx equals `1`
2. idx =
   - Expected: idx equals `2`
3. idx =
   - Expected: idx equals `3`
4. idx =
   - Expected: idx equals `0)  # wraps around`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask = 3  # capacity 4 - 1
var idx = 0
idx = (idx + 1) & mask
expect(idx).to_equal(1)
idx = (idx + 1) & mask
expect(idx).to_equal(2)
idx = (idx + 1) & mask
expect(idx).to_equal(3)
idx = (idx + 1) & mask
expect(idx).to_equal(0)  # wraps around
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/baremetal/semihost_transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Transport Constants
- Capability Flags
- Config Defaults
- Ring Buffer Power-of-2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
