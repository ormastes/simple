# Skia ICC Profile Writer Specification

> Tests for encode_u32_be, encode_s15fixed16, encode_icc_header, and encode_icc_profile — the ICC v4 serialization helpers that form the inverse of the parser in icc_profile.spl.

<!-- sdn-diagram:id=icc_writer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=icc_writer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

icc_writer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=icc_writer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia ICC Profile Writer Specification

Tests for encode_u32_be, encode_s15fixed16, encode_icc_header, and encode_icc_profile — the ICC v4 serialization helpers that form the inverse of the parser in icc_profile.spl.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-012 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/icc_writer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for encode_u32_be, encode_s15fixed16, encode_icc_header, and
encode_icc_profile — the ICC v4 serialization helpers that form the
inverse of the parser in icc_profile.spl.

## Scenarios

### icc_writer

#### encode_u32_be: 0 produces [0,0,0,0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = encode_u32_be(0)
expect(out.length()).to_equal(4)
expect(_byte_at(out, 0)).to_equal(0)
expect(_byte_at(out, 1)).to_equal(0)
expect(_byte_at(out, 2)).to_equal(0)
expect(_byte_at(out, 3)).to_equal(0)
```

</details>

#### encode_u32_be: 0x12345678 produces [0x12, 0x34, 0x56, 0x78]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = encode_u32_be(305419896)
expect(out.length()).to_equal(4)
expect(_byte_at(out, 0)).to_equal(18)    # 0x12
expect(_byte_at(out, 1)).to_equal(52)    # 0x34
expect(_byte_at(out, 2)).to_equal(86)    # 0x56
expect(_byte_at(out, 3)).to_equal(120)   # 0x78
```

</details>

#### encode_s15fixed16: 1.0 produces [0, 1, 0, 0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = encode_s15fixed16(1.0)
expect(out.length()).to_equal(4)
expect(_byte_at(out, 0)).to_equal(0)
expect(_byte_at(out, 1)).to_equal(1)
expect(_byte_at(out, 2)).to_equal(0)
expect(_byte_at(out, 3)).to_equal(0)
```

</details>

#### encode_icc_header: produces 128-byte blob with acsp magic at offset 36

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hdr = encode_icc_header(128, std.skia.entity.color_space.SkColorSpaceKind.Srgb, 1482250784)
expect(hdr.length()).to_equal(128)
# "acsp" = 0x61 0x63 0x73 0x70
expect(_byte_at(hdr, 36)).to_equal(97)   # 0x61
expect(_byte_at(hdr, 37)).to_equal(99)   # 0x63
expect(_byte_at(hdr, 38)).to_equal(115)  # 0x73
expect(_byte_at(hdr, 39)).to_equal(112)  # 0x70
```

</details>

#### encode_icc_profile: for sRGB produces at least 128 bytes and starts with valid header

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = srgb()
val out = encode_icc_profile(cs)
expect(out.length()).to_be_greater_than(127)
# acsp magic at offset 36
expect(_byte_at(out, 36)).to_equal(97)
expect(_byte_at(out, 37)).to_equal(99)
expect(_byte_at(out, 38)).to_equal(115)
expect(_byte_at(out, 39)).to_equal(112)
```

</details>

#### encode_icc_profile: profile_size field in header matches total byte length

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = srgb()
val out = encode_icc_profile(cs)
val total = out.length()
# First 4 bytes = profile size (big-endian u32)
val b0 = _byte_at(out, 0)
val b1 = _byte_at(out, 1)
val b2 = _byte_at(out, 2)
val b3 = _byte_at(out, 3)
val encoded_size = (b0 * 16777216) + (b1 * 65536) + (b2 * 256) + b3
expect(encoded_size).to_equal(total)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
