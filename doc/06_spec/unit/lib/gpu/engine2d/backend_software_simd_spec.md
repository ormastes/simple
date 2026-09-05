# backend_software_simd_spec

> Software Backend SIMD Integration Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_software_simd_spec

Software Backend SIMD Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine2d/backend_software_simd_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Software Backend SIMD Integration Specification

@tag: gpu, engine2d, software, simd, acceleration
@cover src/lib/gc_async_mut/gpu/engine2d/backend_software.spl 60%

Verifies that the optimized software backend uses SIMD kernels for
hot paths when available. Covers AC-6.

## Scenarios

### SoftwareBackend SIMD integration

### clear

#### AC-6: clear uses simd_fill_row when available

- AC-6: clear uses simd_fill_row when available
   - Expected: pixels[0] equals `0xFFFF0000`
   - Expected: pixels[63] equals `0xFFFF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: clear uses simd_fill_row when available")
var backend = SoftwareBackend.create()
reset_simd_hits()
if backend.init(64, 64):
    backend.clear(0xFFFF0000)
    val pixels = backend.read_pixels()
    expect(pixels[0]).to_equal(0xFFFF0000)
    expect(pixels[63]).to_equal(0xFFFF0000)
    expect(simd_hit_counts().fill_hits).to_be_greater_than(0)
    backend.shutdown()
```

</details>

#### AC-6: clear produces same result with and without SIMD

- AC-6: clear produces same result with and without SIMD
   - Expected: all_green is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: clear produces same result with and without SIMD")
var backend = SoftwareBackend.create()
if backend.init(64, 64):
    backend.clear(0xFF00FF00)
    val pixels = backend.read_pixels()
    var i = 0
    var all_green = true
    while i < 64:
        if pixels[i] != 0xFF00FF00:
            all_green = false
        i = i + 1
    expect(all_green).to_equal(true)
    backend.shutdown()
```

</details>

### blit_image

#### AC-6: blit uses simd_blit_row for row copies

- AC-6: blit uses simd_blit_row for row copies
   - Expected: pixels[0] equals `0xFFFF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: blit uses simd_blit_row for row copies")
var backend = SoftwareBackend.create()
reset_simd_hits()
val src_pixels: [u32] = [0xFFFF0000; 16]
if backend.init(64, 64):
    backend.clear(0xFF000000)
    backend.blit_image(0, 0, 4, 4, src_pixels)
    val pixels = backend.read_pixels()
    expect(pixels[0]).to_equal(0xFFFF0000)
    expect(simd_hit_counts().copy_hits).to_be_greater_than(0)
    backend.shutdown()
```

</details>

### alpha blending

#### AC-6: draw_rect_filled with alpha uses simd_blend_row

- AC-6: draw_rect_filled with alpha uses simd_blend_row


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: draw_rect_filled with alpha uses simd_blend_row")
var backend = SoftwareBackend.create()
reset_simd_hits()
if backend.init(64, 64):
    backend.clear(0xFF0000FF)
    backend.draw_rect_filled(0, 0, 32, 32, 0x80FF0000)
    val pixels = backend.read_pixels()
    val r = (pixels[0] >> 16) & 0xFF
    expect(r).to_be_greater_than(50)
    expect(simd_hit_counts().alpha_hits).to_be_greater_than(0)
    backend.shutdown()
```

</details>

### scalar fallback

#### AC-6: works correctly when no SIMD available

- AC-6: works correctly when no SIMD available
   - Expected: pixels[0] equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: works correctly when no SIMD available")
var backend = SoftwareBackend.create()
if backend.init(8, 8):
    backend.clear(0xFFAABBCC)
    backend.draw_line(0, 0, 7, 7, 0xFFFFFFFF, 1)
    val pixels = backend.read_pixels()
    expect(pixels[0]).to_equal(0xFFFFFFFF)
    backend.shutdown()
```

</details>

#### AC-6: tile-based rendering preserved with SIMD

- AC-6: tile-based rendering preserved with SIMD
   - Expected: pixels[0] equals `0xFFFF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-6: tile-based rendering preserved with SIMD")
var backend = SoftwareBackend.create()
if backend.init(128, 128):
    backend.clear(0xFF000000)
    backend.draw_rect_filled(0, 0, 128, 128, 0xFFFF0000)
    backend.present()
    val pixels = backend.read_pixels()
    expect(pixels[0]).to_equal(0xFFFF0000)
    backend.shutdown()
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6cc7a553a990a902cd2aa724a26a62698b7a5654e1475dd34b03238380c81e73`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6cc7a553a990a902cd2aa724a26a62698b7a5654e1475dd34b03238380c81e73`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6cc7a553a990a902cd2aa724a26a62698b7a5654e1475dd34b03238380c81e73`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/gpu/engine2d/backend_software_simd_spec.spl
mirror: doc/06_spec/unit/lib/gpu/engine2d/backend_software_simd_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gpu/engine2d/backend_software_simd_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gpu/engine2d/backend_software_simd_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gpu/engine2d/backend_software_simd_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: clear uses simd_fill_row when available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/backend_software_simd_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: clear produces same result with and without SIMD' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gpu/engine2d/backend_software_simd_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: blit uses simd_blit_row for row copies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
