# simd_kernels_branch_coverage_spec

> engine2d SIMD kernels — decision (branch) coverage completion spec

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simd_kernels_branch_coverage_spec

engine2d SIMD kernels — decision (branch) coverage completion spec

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/simd_kernels_branch_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

engine2d SIMD kernels — decision (branch) coverage completion spec

Targets the both-sides-taken decision-coverage gaps in
src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl left open by the
functional specs: zero/negative counts on every public span fn, all
alpha classes in the blend row (sa==255 / sa==0 / mid over opaque and
transparent dst), scroll up/down/zero/overshoot, blit_rect degenerate
rects, detection caching, and the evidence/validation predicates.

Run under SIMPLE_2D_SIMD=off AND auto (plus forced ISA names) so the
native-vs-scalar routing gates take both sides across the run matrix.

## Scenarios

### span fns: zero and negative counts

#### fill_span ignores count <= 0 and fills count > 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fill_span ignores count <= 0 and fills count > 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fill_span ignores count <= 0 and fills count > 0")
val native = native_pixel_rows_enabled()
var buf: [u32] = [0x11111111; 8]
fill_span(buf, 0, 0, 0xFFAA0000)
fill_span(buf, 0, -3, 0xFFAA0000)
expect buf[0] == 0x11111111u32
fill_span(buf, 2, 3, 0xFFAA0000)
if not native:
    expect buf[1] == 0x11111111u32
    expect buf[2] == 0xFFAA0000u32
    expect buf[4] == 0xFFAA0000u32
    expect buf[5] == 0x11111111u32
_scalar_fill_span(buf, 0, 2, 0xFF0000CC)
expect buf[0] == 0xFF0000CCu32
_scalar_fill_row(buf, 6, 0, 0)
if not native:
    expect buf[6] == 0x11111111u32
```

</details>

#### simd_fill_row rejects count <= 0 directly

- simd_fill_row rejects count <= 0 directly


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("simd_fill_row rejects count <= 0 directly")
val native = native_pixel_rows_enabled()
var buf: [u32] = [7; 4]
simd_fill_row(buf, 0, 0, 0xFF000000)
simd_fill_row(buf, 0, -1, 0xFF000000)
expect buf[0] == 7u32
simd_fill_row(buf, 1, 2, 0xFF010203)
if not native:
    expect buf[1] == 0xFF010203u32
```

</details>

#### copy_span ignores count <= 0 and copies count > 0

- copy_span ignores count <= 0 and copies count > 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("copy_span ignores count <= 0 and copies count > 0")
val native = native_pixel_rows_enabled()
var dst: [u32] = [0; 8]
val src: [u32] = [0xFF112233; 8]
copy_span(dst, 0, src, 0, 0)
copy_span(dst, 0, src, 0, -2)
expect dst[0] == 0u32
copy_span(dst, 1, src, 0, 3)
expect dst[0] == 0u32
if not native:
    expect dst[1] == 0xFF112233u32
    expect dst[3] == 0xFF112233u32
expect dst[4] == 0u32
_scalar_copy_span(dst, 5, src, 0, 1)
expect dst[5] == 0xFF112233u32
```

</details>

#### simd_blit_row rejects count <= 0 directly

- simd_blit_row rejects count <= 0 directly


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("simd_blit_row rejects count <= 0 directly")
val native = native_pixel_rows_enabled()
var dst: [u32] = [1; 4]
val src: [u32] = [9; 4]
simd_blit_row(dst, 0, src, 0, 0)
simd_blit_row(dst, 0, src, 0, -5)
expect dst[0] == 1u32
simd_blit_row(dst, 0, src, 0, 2)
if not native:
    expect dst[0] == 9u32
```

</details>

#### alpha_blend_span ignores count <= 0 and blends count > 0

- alpha_blend_span ignores count <= 0 and blends count > 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("alpha_blend_span ignores count <= 0 and blends count > 0")
val native = native_pixel_rows_enabled()
var dst: [u32] = [0xFF000000; 8]
val src: [u32] = [0xFFFFFFFF; 8]
alpha_blend_span(dst, src, 0, 0)
alpha_blend_span(dst, src, 0, -1)
expect dst[0] == 0xFF000000u32
alpha_blend_span(dst, src, 0, 2)
if not native:
    expect dst[0] == 0xFFFFFFFFu32
expect dst[2] == 0xFF000000u32
_scalar_alpha_blend_span(dst, src, 3, 1)
expect dst[3] == 0xFFFFFFFFu32
```

</details>

#### simd_blend_row rejects count <= 0 directly

- simd_blend_row rejects count <= 0 directly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("simd_blend_row rejects count <= 0 directly")
var dst: [u32] = [0xFF000000; 4]
val src: [u32] = [0xFFFFFFFF; 4]
simd_blend_row(dst, src, 0, 0)
simd_blend_row(dst, src, 0, -4)
expect dst[0] == 0xFF000000u32
```

</details>

### blend alpha classes

#### sa == 255 replaces, sa == 0 leaves, mid alpha mixes over opaque dst

- sa == 255 replaces, sa == 0 leaves, mid alpha mixes over opaque dst


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sa == 255 replaces, sa == 0 leaves, mid alpha mixes over opaque dst")
var dst: [u32] = [0xFF404040; 4]
val src: [u32] = [0xFF102030, 0x00FFFFFF, 0x80FFFFFF, 0x01000000]
_scalar_blend_row(dst, src, 0, 4)
expect dst[0] == 0xFF102030u32
expect dst[1] == 0xFF404040u32
# mid alpha: result strictly between src and dst, opaque out-alpha
val mid = dst[2]
expect ((mid >> 24) & 0xFF) == 255u32
expect ((mid >> 16) & 0xFF) > 0x40u32
expect ((mid >> 16) & 0xFF) < 0xFFu32
# sa == 1 over opaque black stays nearly black but is processed
expect ((dst[3] >> 24) & 0xFF) == 255u32
```

</details>

#### mid alpha over transparent dst keeps src color with src alpha

- mid alpha over transparent dst keeps src color with src alpha


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mid alpha over transparent dst keeps src color with src alpha")
var dst: [u32] = [0x00000000; 2]
val src: [u32] = [0x80AABBCC, 0x80AABBCC]
_scalar_blend_row(dst, src, 0, 2)
expect ((dst[0] >> 24) & 0xFF) == 0x80u32
expect (dst[0] & 0x00FFFFFF) == 0x00AABBCCu32
```

</details>

#### dispatch blend path matches scalar for all alpha classes

- dispatch blend path matches scalar for all alpha classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dispatch blend path matches scalar for all alpha classes")
var a: [u32] = [0xFF404040; 8]
var b: [u32] = [0xFF404040; 8]
val src: [u32] = [0xFF102030, 0x00FFFFFF, 0x80FFFFFF, 0x20112233, 0xFE010203, 0x01FFFFFF, 0x7F808080, 0xC0C0C0C0]
simd_blend_row(a, src, 0, 8)
_scalar_blend_row(b, src, 0, 8)
if not native_pixel_rows_enabled():
    var i = 0
    var same = true
    while i < 8:
        if a[i] != b[i]:
            same = false
        i = i + 1
    expect same
```

</details>

### blit_rect degenerate and positive rects

#### simd_blit_rect skips w <= 0 or h <= 0 and copies positive rects

- simd_blit_rect skips w <= 0 or h <= 0 and copies positive rects


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("simd_blit_rect skips w <= 0 or h <= 0 and copies positive rects")
val native = native_pixel_rows_enabled()
var dst: [u32] = [0; 16]
val src: [u32] = [0xFFABCDEF; 16]
simd_blit_rect(dst, 4, 0, 0, src, 4, 0, 0, 0, 2)
simd_blit_rect(dst, 4, 0, 0, src, 4, 0, 0, -1, 2)
simd_blit_rect(dst, 4, 0, 0, src, 4, 0, 0, 2, 0)
simd_blit_rect(dst, 4, 0, 0, src, 4, 0, 0, 2, -2)
expect dst[0] == 0u32
simd_blit_rect(dst, 4, 1, 1, src, 4, 0, 0, 2, 2)
if not native:
    expect dst[5] == 0xFFABCDEFu32
    expect dst[10] == 0xFFABCDEFu32
expect dst[0] == 0u32
```

</details>

#### blit_rect wrapper and scalar reference behave identically

- blit_rect wrapper and scalar reference behave identically


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blit_rect wrapper and scalar reference behave identically")
var d1: [u32] = [0; 16]
var d2: [u32] = [0; 16]
val src: [u32] = [0xFF031415; 16]
blit_rect(d1, 4, 0, 0, src, 4, 0, 0, 3, 3)
_scalar_blit_rect(d2, 4, 0, 0, src, 4, 0, 0, 3, 3)
_scalar_blit_rect(d2, 4, 0, 0, src, 4, 0, 0, 0, 3)
_scalar_blit_rect(d2, 4, 0, 0, src, 4, 0, 0, 3, 0)
if not native_pixel_rows_enabled():
    var i = 0
    var same = true
    while i < 16:
        if d1[i] != d2[i]:
            same = false
        i = i + 1
    expect same
_scalar_blit_row(d2, 0, src, 0, 0)
expect d2[0] == 0xFF031415u32
```

</details>

### scroll_region direction and degenerate cases

#### skips w <= 0, h <= 0 and delta_y == 0

- skips w <= 0, h <= 0 and delta_y == 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips w <= 0, h <= 0 and delta_y == 0")
var buf = ramp16()
simd_scroll_region(buf, 4, 0, 0, 0, 4, 1)
simd_scroll_region(buf, 4, 0, 0, -2, 4, 1)
simd_scroll_region(buf, 4, 0, 0, 4, 0, 1)
simd_scroll_region(buf, 4, 0, 0, 4, -1, 1)
simd_scroll_region(buf, 4, 0, 0, 4, 4, 0)
expect buf[0] == 0xFF000000u32
expect buf[15] == 0xFF00000Fu32
```

</details>

#### overshoot delta (|dy| >= h) records the hit but copies nothing

- overshoot delta (|dy| >= h) records the hit but copies nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("overshoot delta (|dy| >= h) records the hit but copies nothing")
var buf = ramp16()
simd_scroll_region(buf, 4, 0, 0, 4, 4, 5)
simd_scroll_region(buf, 4, 0, 0, 4, 4, -4)
expect buf[0] == 0xFF000000u32
expect buf[12] == 0xFF00000Cu32
```

</details>

#### scrolls up (negative) and down (positive)

- scrolls up (negative) and down (positive)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scrolls up (negative) and down (positive)")
var up = ramp16()
simd_scroll_region(up, 4, 0, 0, 4, 4, -1)
expect up[0] == 0xFF000004u32
expect up[8] == 0xFF00000Cu32
var down = ramp16()
scroll_region(down, 4, 0, 0, 4, 4, 1)
expect down[4] == 0xFF000000u32
expect down[12] == 0xFF000008u32
```

</details>

#### scalar reference takes the same branch set

- scalar reference takes the same branch set


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scalar reference takes the same branch set")
var buf = ramp16()
_scalar_scroll_region(buf, 4, 0, 0, 0, 4, 1)
_scalar_scroll_region(buf, 4, 0, 0, 4, 0, 1)
_scalar_scroll_region(buf, 4, 0, 0, 4, 4, 0)
_scalar_scroll_region(buf, 4, 0, 0, 4, 4, 9)
expect buf[0] == 0xFF000000u32
_scalar_scroll_region(buf, 4, 0, 0, 4, 4, -1)
expect buf[0] == 0xFF000004u32
var down = ramp16()
_scalar_scroll_region(down, 4, 0, 0, 4, 4, 2)
expect down[8] == 0xFF000000u32
```

</details>

### detection, config and routing gates

#### detect_simd_level is cached across calls

- detect_simd_level is cached across calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detect_simd_level is cached across calls")
val first = detect_simd_level()
val second = detect_simd_level()
expect first.to_text() == second.to_text()
```

</details>

#### level texts stay consistent for the active level

- level texts stay consistent for the active level


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("level texts stay consistent for the active level")
val level = detect_simd_level()
expect level.to_text().len() > 0
expect level.arch_text().len() > 0
expect level.feature_text().len() > 0
expect active_feature_text() == level.feature_text()
expect active_arch_text() == level.arch_text()
val feats = active_target_features()
expect feats.len() == 1
expect feats[0] == level.feature_text()
```

</details>

#### all six SimdLevel variants render all three texts

- all six SimdLevel variants render all three texts


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("all six SimdLevel variants render all three texts")
val levels = [SimdLevel.None_, SimdLevel.Sse42, SimdLevel.Avx2, SimdLevel.Avx512, SimdLevel.Neon, SimdLevel.Rvv]
val names = ["None", "SSE4.2", "AVX2", "AVX-512", "NEON", "RVV"]
val archs = ["unknown", "x86_64", "x86_64", "x86_64", "aarch64", "riscv64"]
val feats = ["scalar", "sse42", "avx2", "avx2", "neon", "rvv"]
var i = 0
var ok = true
while i < 6:
    if levels[i].to_text() != names[i]:
        ok = false
    if levels[i].arch_text() != archs[i]:
        ok = false
    if levels[i].feature_text() != feats[i]:
        ok = false
    i = i + 1
expect ok
```

</details>

#### simd_config_mode and native routing gate agree with the env

- simd_config_mode and native routing gate agree with the env


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("simd_config_mode and native routing gate agree with the env")
val mode = simd_config_mode()
expect mode.len() > 0
val enabled = native_pixel_rows_enabled()
val cached = native_pixel_rows_enabled()
expect enabled == cached
if mode == "off":
    expect enabled == false
```

</details>

#### _forced_simd_level maps each explicit ISA name and rejects the rest

- _forced_simd_level maps each explicit ISA name and rejects the rest


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("_forced_simd_level maps each explicit ISA name and rejects the rest")
expect _forced_simd_level("sse2").to_text() == "SSE4.2"
expect _forced_simd_level("avx2").to_text() == "AVX2"
expect _forced_simd_level("neon").to_text() == "NEON"
expect _forced_simd_level("rvv").to_text() == "RVV"
expect _forced_simd_level("auto").to_text() == "None"
expect _forced_simd_level("off").to_text() == "None"
expect _forced_simd_level("bogus").to_text() == "None"
```

</details>

#### an unknown SIMPLE_2D_SIMD name never forces a level

- an unknown SIMPLE_2D_SIMD name never forces a level


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an unknown SIMPLE_2D_SIMD name never forces a level")
# Run the matrix with SIMPLE_2D_SIMD=bogus to drive detect_simd_level's
# forced-name gate (line 151) down its false side: an unknown name is
# not auto/off, but _forced_simd_level returns None_, so detection
# falls through to the host CPU probes.
val mode = simd_config_mode()
if mode != "auto" and mode != "off":
    if _forced_simd_level(mode).to_text() == "None":
        # unknown name: the detected level must be host-derived, never None-forced text mismatch
        expect detect_simd_level().feature_text().len() > 0
```

</details>

#### feature probes return stable booleans

- feature probes return stable booleans


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("feature probes return stable booleans")
expect engine2d_simd_has_sse() == engine2d_simd_has_sse()
expect engine2d_simd_has_avx2() == engine2d_simd_has_avx2()
expect engine2d_simd_has_neon() == engine2d_simd_has_neon()
expect engine2d_simd_has_rvv() == engine2d_simd_has_rvv()
```

</details>

### evidence and validation predicates

#### _bool_text renders both sides

- _bool_text renders both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("_bool_text renders both sides")
expect _bool_text(true) == "true"
expect _bool_text(false) == "false"
```

</details>

#### _cpu_simd_checksum handles empty and non-empty buffers

- _cpu_simd_checksum handles empty and non-empty buffers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("_cpu_simd_checksum handles empty and non-empty buffers")
val empty: [u32] = []
expect _cpu_simd_checksum(empty) == 0
val one: [u32] = [0x00010101]
expect _cpu_simd_checksum(one) == 9
```

</details>

#### executed_all needs every kernel flag

- executed_all needs every kernel flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executed_all needs every kernel flag")
val full = mk_evidence("x86_64", "avx2", true, true, true, 4)
expect full.executed_all()
var partial = mk_evidence("x86_64", "avx2", true, true, true, 4)
partial.executed_scroll = false
expect partial.executed_all() == false
partial.executed_alpha = false
partial.executed_copy = false
partial.executed_fill = false
expect partial.executed_all() == false
expect partial.diagnostic_text().len() > 0
```

</details>

#### cpu_simd_required_evidence_valid takes both verdicts

- cpu_simd_required_evidence_valid takes both verdicts


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cpu_simd_required_evidence_valid takes both verdicts")
val good = mk_evidence("x86_64", "avx2", true, true, true, 4)
expect cpu_simd_required_evidence_valid(good, "x86_64", 0)
expect cpu_simd_required_evidence_valid(good, "aarch64", 0) == false
expect cpu_simd_required_evidence_valid(good, "x86_64", 3) == false
val no_hits = mk_evidence("x86_64", "avx2", true, true, true, 0)
expect cpu_simd_required_evidence_valid(no_hits, "x86_64", 0) == false
val not_exact = mk_evidence("x86_64", "avx2", true, true, false, 4)
expect cpu_simd_required_evidence_valid(not_exact, "x86_64", 0) == false
val not_native = mk_evidence("x86_64", "avx2", true, false, true, 4)
expect cpu_simd_required_evidence_valid(not_native, "x86_64", 0) == false
val not_run = mk_evidence("x86_64", "avx2", false, true, true, 4)
expect cpu_simd_required_evidence_valid(not_run, "x86_64", 0) == false
```

</details>

#### runtime evidence is internally consistent

- runtime evidence is internally consistent


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runtime evidence is internally consistent")
val ev = cpu_simd_runtime_evidence()
expect ev.executed_fill
expect ev.executed_copy
expect ev.executed_alpha
expect ev.executed_scroll
expect ev.reason.len() > 0
expect ev.diagnostic_text().len() > 0
val native = native_simd_pixel_evidence()
if detect_simd_level() == SimdLevel.None_:
    expect native.executed == false
    expect native.hits == 0
else:
    expect native.bit_exact
```

</details>

#### CpuSimdProvider forwards hit counts and features

- CpuSimdProvider forwards hit counts and features


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CpuSimdProvider forwards hit counts and features")
val provider = make_cpu_simd_provider()
val counts = provider.hit_counts()
expect counts.fill_hits >= 0
val feats = provider.target_features()
expect feats.len() == 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d03c66d4e0073f939b3261ac511eb2a03fb17b487b2bb85581668edab4d3ffff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d03c66d4e0073f939b3261ac511eb2a03fb17b487b2bb85581668edab4d3ffff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d03c66d4e0073f939b3261ac511eb2a03fb17b487b2bb85581668edab4d3ffff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/simd_kernels_branch_coverage_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/simd_kernels_branch_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/simd_kernels_branch_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/simd_kernels_branch_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/simd_kernels_branch_coverage_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fill_span ignores count <= 0 and fills count > 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/simd_kernels_branch_coverage_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simd_fill_row rejects count <= 0 directly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/simd_kernels_branch_coverage_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copy_span ignores count <= 0 and copies count > 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
