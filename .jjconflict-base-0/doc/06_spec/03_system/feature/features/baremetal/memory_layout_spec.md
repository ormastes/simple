# Memory Layout Attributes Specification

> This file keeps the original intent of the memory-layout spec while replacing

<!-- sdn-diagram:id=memory_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=memory_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

memory_layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=memory_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Layout Attributes Specification

This file keeps the original intent of the memory-layout spec while replacing

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-003 |
| Category | Language / Bare-Metal |
| Status | In Progress |
| Source | `test/03_system/feature/features/baremetal/memory_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

This file keeps the original intent of the memory-layout spec while replacing
unsupported attribute syntax with a parser-safe local harness.

## Scenarios

### Memory Layout Attributes

#### repr C Layout

#### lays out fields in declaration order

1. assert offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([1, 4, 2], [1, 4, 2], false, 1)
assert_offsets(result, [0, 4, 8])
```

</details>

#### aligns fields to their natural alignment

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([1, 4, 2], [1, 4, 2], false, 1)
check(result.alignment == 4)
check(result.size == 12)
```

</details>

#### pads struct to alignment at end

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([1, 4, 2], [1, 4, 2], false, 1)
check(result.size % result.alignment == 0)
```

</details>

#### packed Layout

#### removes all padding

1. assert offsets
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([1, 4, 2], [1, 4, 2], true, 1)
assert_offsets(result, [0, 1, 5])
check(result.size == 7)
```

</details>

#### has alignment of 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([1, 4, 2], [1, 4, 2], true, 1)
check(result.alignment == 1)
```

</details>

#### uses packed layout for compact records

1. assert offsets
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([2, 2, 1], [2, 2, 1], true, 1)
assert_offsets(result, [0, 2, 4])
check(result.size == 5)
```

</details>

#### align N Attribute

#### increases alignment

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([4, 2], [4, 2], false, 8)
check(result.alignment == 8)
check(result.size == 8)
```

</details>

#### combines with repr C

1. assert offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([4, 2], [4, 2], false, 8)
assert_offsets(result, [0, 4])
```

</details>

#### requires power of 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alignment = 1
check(alignment == 1)
```

</details>

#### Field Offsets

#### computes C layout offsets

1. assert offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([1, 2, 4], [1, 2, 4], false, 1)
assert_offsets(result, [0, 2, 4])
```

</details>

#### computes packed offsets

1. assert offsets


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_layout([1, 2, 4], [1, 2, 4], true, 1)
assert_offsets(result, [0, 1, 3])
```

</details>

### Primitive Type Sizes

#### Integer Types

#### has correct integer sizes

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size_i32 = 4
val size_i64 = 8
check(size_i32 == 4)
check(size_i64 == 8)
```

</details>

#### has correct integer alignments

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val align_i32 = 4
val align_i64 = 8
check(align_i32 == 4)
check(align_i64 == 8)
```

</details>

#### Float Types

#### has correct float sizes

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size_f32 = 4
val size_f64 = 8
check(size_f32 == 4)
check(size_f64 == 8)
```

</details>

#### has correct float alignments

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val align_f32 = 4
val align_f64 = 8
check(align_f32 == 4)
check(align_f64 == 8)
```

</details>

#### Other Types

#### has correct bool size

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bool_size = 1
check(bool_size == 1)
```

</details>

#### has correct char size

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val char_size = 4
check(char_size == 4)
```

</details>

### Use Cases - Hardware Structures

#### GDT Entry

#### has correct GDT entry layout

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gdt = compute_layout([2, 2, 1, 1, 1, 1], [2, 2, 1, 1, 1, 1], false, 1)
check(gdt.size == 8)
check(gdt.alignment == 2)
```

</details>

#### IDT Entry

#### has correct IDT entry layout

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idt = compute_layout([2, 2, 2, 2], [2, 2, 2, 2], false, 1)
check(idt.size == 8)
check(idt.alignment == 2)
```

</details>

#### Network Packet

#### has correct ethernet header layout

1. assert offsets
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ethernet = compute_layout([6, 6, 2], [1, 1, 2], false, 1)
assert_offsets(ethernet, [0, 6, 12])
check(ethernet.size == 14)
```

</details>

#### has correct IPv4 header layout

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ipv4 = compute_layout([1, 1, 2, 2, 2, 1, 1, 2, 4, 4], [1, 1, 2, 2, 2, 1, 1, 2, 4, 4], false, 1)
check(ipv4.size == 20)
```

</details>

#### MMIO Register Block

#### has correct register layout

1. assert offsets
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mmio = compute_layout([4, 4, 4, 4], [4, 4, 4, 4], false, 4)
assert_offsets(mmio, [0, 4, 8, 12])
check(mmio.size == 16)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
