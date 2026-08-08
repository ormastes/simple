# Byte Utilities

> Verifies shared little-endian byte helpers used by ELF64, SMF, and

<!-- sdn-diagram:id=byte_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=byte_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

byte_utils_spec -> std
byte_utils_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=byte_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Byte Utilities

Verifies shared little-endian byte helpers used by ELF64, SMF, and

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G10-BYTEUTILS |
| Category | Kernel loader |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/byte_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies shared little-endian byte helpers used by ELF64, SMF, and
ELF loader modules.

## Scenarios

### byte_utils

#### byte_at reads individual bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _sample_bytes()
expect(byte_at(data, 0)).to_equal(0x01.to_u8())
expect(byte_at(data, 7)).to_equal(0x08.to_u8())
```

</details>

#### read_u16_le decodes little-endian u16

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _sample_bytes()
# 0x01 | (0x02 << 8) = 0x0201 = 513
expect(read_u16_le(data, 0)).to_equal(513)
```

</details>

#### read_u32_le decodes little-endian u32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _sample_bytes()
# 0x01 | (0x02 << 8) | (0x03 << 16) | (0x04 << 24) = 0x04030201 = 67305985
expect(read_u32_le(data, 0)).to_equal(67305985)
```

</details>

#### read_u64_le decodes little-endian u64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _sample_bytes()
# 0x0807060504030201
expect(read_u64_le(data, 0)).to_equal(578437695752307201)
```

</details>

#### patch_u32_le writes little-endian u32

1. data push
2. data push
3. data push
4. data push
5. data = patch u32 le
   - Expected: byte_at(data, 0) equals `0x01.to_u8()`
   - Expected: byte_at(data, 1) equals `0x02.to_u8()`
   - Expected: byte_at(data, 2) equals `0x03.to_u8()`
   - Expected: byte_at(data, 3) equals `0x04.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data.push(0.to_u8())
data.push(0.to_u8())
data.push(0.to_u8())
data.push(0.to_u8())
data = patch_u32_le(data, 0, 0x04030201)
expect(byte_at(data, 0)).to_equal(0x01.to_u8())
expect(byte_at(data, 1)).to_equal(0x02.to_u8())
expect(byte_at(data, 2)).to_equal(0x03.to_u8())
expect(byte_at(data, 3)).to_equal(0x04.to_u8())
```

</details>

#### patch_u64_le writes little-endian u64

1. data push
2. data = patch u64 le
   - Expected: byte_at(data, 0) equals `0x01.to_u8()`
   - Expected: byte_at(data, 7) equals `0x08.to_u8()`
   - Expected: read_u64_le(data, 0) equals `578437695752307201`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
var i = 0
while i < 8:
    data.push(0.to_u8())
    i = i + 1
data = patch_u64_le(data, 0, 0x0807060504030201)
expect(byte_at(data, 0)).to_equal(0x01.to_u8())
expect(byte_at(data, 7)).to_equal(0x08.to_u8())
expect(read_u64_le(data, 0)).to_equal(578437695752307201)
```

</details>

#### has_magic checks 4-byte magic at offset

1. data push
2. data push
3. data push
4. data push
   - Expected: has_magic(data, 0, 0x7F.to_u8(), 0x45.to_u8(), 0x4C.to_u8(), 0x46.to_u8()) is true
   - Expected: has_magic(data, 0, 0x00.to_u8(), 0x45.to_u8(), 0x4C.to_u8(), 0x46.to_u8()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data.push(0x7F.to_u8())
data.push(0x45.to_u8())
data.push(0x4C.to_u8())
data.push(0x46.to_u8())
expect(has_magic(data, 0, 0x7F.to_u8(), 0x45.to_u8(), 0x4C.to_u8(), 0x46.to_u8())).to_equal(true)
expect(has_magic(data, 0, 0x00.to_u8(), 0x45.to_u8(), 0x4C.to_u8(), 0x46.to_u8())).to_equal(false)
```

</details>

#### has_magic rejects out-of-bounds offsets

1. data push
   - Expected: has_magic(data, 0, 0x7F.to_u8(), 0x45.to_u8(), 0x4C.to_u8(), 0x46.to_u8()) is false
   - Expected: has_magic(data, -1, 0x7F.to_u8(), 0x45.to_u8(), 0x4C.to_u8(), 0x46.to_u8()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data.push(0x7F.to_u8())
expect(has_magic(data, 0, 0x7F.to_u8(), 0x45.to_u8(), 0x4C.to_u8(), 0x46.to_u8())).to_equal(false)
expect(has_magic(data, -1, 0x7F.to_u8(), 0x45.to_u8(), 0x4C.to_u8(), 0x46.to_u8())).to_equal(false)
```

</details>

#### in_range validates byte ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _sample_bytes()
expect(in_range(data, 0, 8)).to_equal(true)
expect(in_range(data, 0, 9)).to_equal(false)
expect(in_range(data, 7, 1)).to_equal(true)
expect(in_range(data, -1, 1)).to_equal(false)
expect(in_range(data, 0, -1)).to_equal(false)
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
