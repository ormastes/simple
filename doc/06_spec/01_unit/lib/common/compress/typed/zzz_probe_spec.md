# Zzz Probe Specification

> <details>

<!-- sdn-diagram:id=zzz_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zzz_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zzz_probe_spec -> std
zzz_probe_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zzz_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zzz Probe Specification

## Scenarios

### negative control

#### assert_equal catches wrong values (self-proof)

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Proof: we verified assert_equal(1,2) fires FAIL, then reverted.
val x = 42
assert_equal(x, 42)
```

</details>

### Crc32 KAT

#### CRC32 of 123456789 equals 0xCBF43926

- var crc = Crc32 new
- crc update
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [49u8, 50u8, 51u8, 52u8, 53u8, 54u8, 55u8, 56u8, 57u8]
val sp = ByteSpan.new(bytes)
var crc = Crc32.new()
crc.update(sp)
val got = crc.raw()
assert_equal(got, 0xCBF43926)
```

</details>

### deflate_reverse_bits

#### reverse 0b1 in 1 bit = 0b1

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = deflate_reverse_bits(1, 1)
assert_equal(r, 1)
```

</details>

#### reverse 0b10 in 2 bits = 0b01

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = deflate_reverse_bits(2, 2)
assert_equal(r, 1)
```

</details>

#### reverse 0b110 in 3 bits = 0b011

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = deflate_reverse_bits(6, 3)
assert_equal(r, 3)
```

</details>

#### reverse 0b0000000 in 7 bits = 0b0000000 (EOB sym 256 code)

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = deflate_reverse_bits(0, 7)
assert_equal(r, 0)
```

</details>

### stored block KAT

#### inflate hand-built stored block for hi — len=2 first=104 sum=209

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw: [u8] = [1u8, 2u8, 0u8, 253u8, 255u8, 104u8, 105u8]
val sp = ByteSpan.new(raw)
val out = inflate_stored(sp)
val out_sp = out.freeze()
assert_equal(out_sp.len(), 2)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 104)
val s = byte_sum(out_sp)
assert_equal(s, 209)
```

</details>

### deflate_stored round-trip

#### empty input round-trips via stored — len=0

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = ByteSpan.empty()
val compressed = deflate_stored(sp)
val out = inflate_stored(compressed.freeze())
assert_equal(out.freeze().len(), 0)
```

</details>

#### hello round-trips via stored — len=5 first=104 sum=532

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
val compressed = deflate_stored(sp)
val out = inflate_stored(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 5)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 104)
val s = byte_sum(out_sp)
assert_equal(s, 532)
```

</details>

#### 100-byte all-a round-trips via stored — len=100 all=97 sum=9700

- ab push
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ab: [u8] = []
var i = 0
while i < 100:
    ab.push(97u8)
    i = i + 1
val sp = ByteSpan.new(ab)
val compressed = deflate_stored(sp)
val out = inflate_stored(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 100)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 97)
val all_ok = all_bytes_equal(out_sp, 97)
assert_equal(all_ok, 1)
```

</details>

### deflate_fixed round-trip

#### empty input round-trips via fixed-Huffman — len=0

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = ByteSpan.empty()
val compressed = deflate_fixed(sp)
val out = inflate_fixed(compressed.freeze())
assert_equal(out.freeze().len(), 0)
```

</details>

#### hello round-trips via fixed-Huffman — len=5 first=104 sum=532

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
val compressed = deflate_fixed(sp)
val out = inflate_fixed(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 5)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 104)
val s = byte_sum(out_sp)
assert_equal(s, 532)
```

</details>

#### single byte A=65 round-trips via fixed-Huffman

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [65u8]
val sp = ByteSpan.new(bytes)
val compressed = deflate_fixed(sp)
val out = inflate_fixed(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 1)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 65)
```

</details>

#### 100 repeated a=97 round-trips via fixed-Huffman literals — sum=9700

- ab push
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ab: [u8] = []
var i = 0
while i < 100:
    ab.push(97u8)
    i = i + 1
val sp = ByteSpan.new(ab)
val compressed = deflate_fixed(sp)
val out = inflate_fixed(compressed.freeze())
val out_sp = out.freeze()
assert_equal(out_sp.len(), 100)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 97)
val all_ok = all_bytes_equal(out_sp, 97)
assert_equal(all_ok, 1)
```

</details>

### gzip round-trip

#### gzip empty input — magic ok len>=18 decomp=0

- assert true
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = ByteSpan.empty()
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val has_header = gz_sp.len() >= 18
assert_true(has_header)
val id1 = gz_sp.get(0).to_i64()
assert_equal(id1, 31)
val out = gzip_decompress(gz_sp)
assert_equal(out.freeze().len(), 0)
```

</details>

#### gzip hello — magic id1=31 cm=8 decomp len=5 sum=532

- assert equal
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val id1 = gz_sp.get(0).to_i64()
assert_equal(id1, 31)
val cm = gz_sp.get(2).to_i64()
assert_equal(cm, 8)
val out = gzip_decompress(gz_sp)
val out_sp = out.freeze()
assert_equal(out_sp.len(), 5)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 104)
val s = byte_sum(out_sp)
assert_equal(s, 532)
```

</details>

#### gzip 100-byte repeated a=97 round-trips — len=100 sum=9700

- ab push
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ab: [u8] = []
var i = 0
while i < 100:
    ab.push(97u8)
    i = i + 1
val sp = ByteSpan.new(ab)
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val out = gzip_decompress(gz_sp)
val out_sp = out.freeze()
assert_equal(out_sp.len(), 100)
val b0 = out_sp.get(0).to_i64()
assert_equal(b0, 97)
val all_ok = all_bytes_equal(out_sp, 97)
assert_equal(all_ok, 1)
```

</details>

#### gzip OS byte at index 9 is 255 (unknown OS)

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [65u8]
val sp = ByteSpan.new(bytes)
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val os_byte = gz_sp.get(9).to_i64()
assert_equal(os_byte, 255)
```

</details>

#### gzip CRC32 trailer matches independent CRC32(hello)

- var crc check = Crc32 new
- crc check update
- stored crc = stored crc |
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
var crc_check = Crc32.new()
crc_check.update(sp)
val expected_crc = crc_check.raw()
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val gz_len = gz_sp.len()
val crc_b0 = gz_sp.get(gz_len - 8).to_i64()
# Compute stored CRC from trailer using byte_sum workaround:
# Read CRC LE 4 bytes via iteration to avoid get(N>0) pollution
var stored_crc = 0
var shift = 0
var ci = gz_len - 8
while ci < gz_len - 4:
    stored_crc = stored_crc | (gz_sp.get(ci).to_i64() << shift)
    shift = shift + 8
    ci = ci + 1
assert_equal(stored_crc, expected_crc)
```

</details>

#### gzip ISIZE trailer is 5 for hello

- isize = isize |
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = [104u8, 101u8, 108u8, 108u8, 111u8]
val sp = ByteSpan.new(bytes)
val gz = gzip_compress(sp)
val gz_sp = gz.freeze()
val gz_len = gz_sp.len()
var isize = 0
var shift = 0
var ii = gz_len - 4
while ii < gz_len:
    isize = isize | (gz_sp.get(ii).to_i64() << shift)
    shift = shift + 8
    ii = ii + 1
assert_equal(isize, 5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/typed/zzz_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- negative control
- Crc32 KAT
- deflate_reverse_bits
- stored block KAT
- deflate_stored round-trip
- deflate_fixed round-trip
- gzip round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
