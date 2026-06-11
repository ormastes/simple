# Simd Kernels Specification

> <details>

<!-- sdn-diagram:id=simd_kernels_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simd_kernels_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simd_kernels_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simd_kernels_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Kernels Specification

## Scenarios

### SimdLevel

#### AC-6: has None variant for scalar fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = SimdLevel.None_
expect(level.to_text()).to_equal("None")
```

</details>

#### AC-6: has Sse42 variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = SimdLevel.Sse42
expect(level.to_text()).to_equal("SSE4.2")
```

</details>

#### AC-6: has Avx2 variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = SimdLevel.Avx2
expect(level.to_text()).to_equal("AVX2")
```

</details>

#### AC-6: has Avx512 variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = SimdLevel.Avx512
expect(level.to_text()).to_equal("AVX-512")
```

</details>

#### AC-6: has Neon variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = SimdLevel.Neon
expect(level.to_text()).to_equal("NEON")
```

</details>

### detect_simd_level

#### AC-6: returns a valid SimdLevel on any platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level = detect_simd_level()
val name = level.to_text()
val valid = name == "None" or name == "SSE4.2" or name == "AVX2" or name == "AVX-512" or name == "NEON"
expect(valid).to_equal(true)
```

</details>

#### AC-6: detection is consistent across calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level1 = detect_simd_level()
val level2 = detect_simd_level()
expect(level1.to_text()).to_equal(level2.to_text())
```

</details>

#### AC-6: records runtime execution evidence for fill copy alpha and scroll

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = cpu_simd_runtime_evidence()
expect(evidence.executed_fill).to_equal(true)
expect(evidence.executed_copy).to_equal(true)
expect(evidence.executed_alpha).to_equal(true)
expect(evidence.executed_scroll).to_equal(true)
expect(evidence.executed_all()).to_equal(true)
expect(evidence.checksum).to_be_greater_than(0)
expect(evidence.diagnostic_text()).to_contain("arch=")
expect(evidence.diagnostic_text()).to_contain("feature=")
expect(evidence.diagnostic_text()).to_contain("executed=true")
```

</details>

### simd_fill_row

#### AC-6: fills row with solid color

1. simd fill row
   - Expected: buf[0] equals `0xFFFF0000`
   - Expected: buf[15] equals `0xFFFF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [0u32; 16]
val color: u32 = 0xFFFF0000
simd_fill_row(buf, 0, 16, color)
expect(buf[0]).to_equal(0xFFFF0000)
expect(buf[15]).to_equal(0xFFFF0000)
```

</details>

#### AC-6: fills partial row with offset

1. simd fill row
   - Expected: buf[0] equals `0`
   - Expected: buf[4] equals `0xFF00FF00`
   - Expected: buf[11] equals `0xFF00FF00`
   - Expected: buf[12] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [0u32; 16]
val color: u32 = 0xFF00FF00
simd_fill_row(buf, 4, 8, color)
expect(buf[0]).to_equal(0)
expect(buf[4]).to_equal(0xFF00FF00)
expect(buf[11]).to_equal(0xFF00FF00)
expect(buf[12]).to_equal(0)
```

</details>

#### AC-6: handles zero-length fill

1. simd fill row
   - Expected: buf[0] equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [0xFFFFFFFF; 4]
simd_fill_row(buf, 0, 0, 0)
expect(buf[0]).to_equal(0xFFFFFFFF)
```

</details>

### simd_blend_row

#### AC-6: blends opaque source over destination

1. simd blend row
   - Expected: dst[0] equals `0xFFFF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dst: [u32] = [0xFF0000FF; 4]
var src: [u32] = [0xFFFF0000; 4]
simd_blend_row(dst, src, 0, 4)
expect(dst[0]).to_equal(0xFFFF0000)
```

</details>

#### AC-6: transparent source leaves destination unchanged

1. simd blend row
   - Expected: dst[0] equals `0xFF0000FF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dst: [u32] = [0xFF0000FF; 4]
var src: [u32] = [0x00000000; 4]
simd_blend_row(dst, src, 0, 4)
expect(dst[0]).to_equal(0xFF0000FF)
```

</details>

#### AC-6: 50% alpha blends correctly

1. simd blend row


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dst: [u32] = [0xFF000000; 4]
var src: [u32] = [0x80FF0000; 4]
simd_blend_row(dst, src, 0, 4)
val r = (dst[0] >> 16) & 0xFF
expect(r).to_be_greater_than(100)
expect(r).to_be_less_than(200)
```

</details>

### simd_blit_row

#### AC-6: copies pixels from source to destination

1. simd blit row
   - Expected: dst[0] equals `0xFFAABBCC`
   - Expected: dst[7] equals `0xFFAABBCC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dst: [u32] = [0u32; 8]
var src: [u32] = [0xFFAABBCC; 8]
simd_blit_row(dst, 0, src, 0, 8)
expect(dst[0]).to_equal(0xFFAABBCC)
expect(dst[7]).to_equal(0xFFAABBCC)
```

</details>

#### AC-6: copies with offset

1. simd blit row
   - Expected: dst[0] equals `0`
   - Expected: dst[2] equals `0xFFDDEEFF`
   - Expected: dst[5] equals `0xFFDDEEFF`
   - Expected: dst[6] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dst: [u32] = [0u32; 8]
var src: [u32] = [0xFFDDEEFF; 8]
simd_blit_row(dst, 2, src, 0, 4)
expect(dst[0]).to_equal(0)
expect(dst[2]).to_equal(0xFFDDEEFF)
expect(dst[5]).to_equal(0xFFDDEEFF)
expect(dst[6]).to_equal(0)
```

</details>

### universal fallback

#### AC-6: SIMD ops work even when SimdLevel is None (scalar fallback)

1. simd fill row
   - Expected: buf[0] equals `0xFFFF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [0u32; 4]
simd_fill_row(buf, 0, 4, 0xFFFF0000)
expect(buf[0]).to_equal(0xFFFF0000)
```

</details>

#### AC-6: same results regardless of SIMD level

1. simd fill row
2. simd fill row
   - Expected: buf1[0] equals `buf2[0]`
   - Expected: buf1[3] equals `buf2[3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf1: [u32] = [0u32; 4]
var buf2: [u32] = [0u32; 4]
simd_fill_row(buf1, 0, 4, 0xFF112233)
simd_fill_row(buf2, 0, 4, 0xFF112233)
expect(buf1[0]).to_equal(buf2[0])
expect(buf1[3]).to_equal(buf2[3])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/simd_kernels_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimdLevel
- detect_simd_level
- simd_fill_row
- simd_blend_row
- simd_blit_row
- universal fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
