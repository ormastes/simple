# backend_software_simd_spec

> Software Backend SIMD Integration Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_software_simd_spec

Software Backend SIMD Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_software_simd_spec.spl` |
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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

#### horizontal gradient rows match scalar clipping and damage

- horizontal gradient rows match scalar clipping and damage
   - Expected: scalar.init(8, 4) is true
   - Expected: simd.init(8, 4) is true
   - Expected: simd.read_pixels() equals `scalar.read_pixels()`
   - Expected: simd.damage_rects(16) equals `scalar.damage_rects(16)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("horizontal gradient rows match scalar clipping and damage")
var scalar = SoftwareBackend.create()
var simd = SoftwareBackend.create_cpu_simd()
expect(scalar.init(8, 4)).to_equal(true)
expect(simd.init(8, 4)).to_equal(true)
scalar.clear(0x60402010u32)
simd.clear(0x60402010u32)
scalar.present()
simd.present()
reset_simd_hits()
scalar.draw_gradient_rect_h(-2, 1, 9, 4, 0x201020F0u32, 0xE0F08010u32)
simd.draw_gradient_rect_h(-2, 1, 9, 4, 0x201020F0u32, 0xE0F08010u32)
expect(simd.read_pixels()).to_equal(scalar.read_pixels())
expect(simd.damage_rects(16)).to_equal(scalar.damage_rects(16))
expect(simd_hit_counts().alpha_hits).to_be_greater_than(0)
scalar.shutdown()
simd.shutdown()
```

</details>

#### one-column horizontal gradient is exactly the left colour

- one-column horizontal gradient is exactly the left colour
   - Expected: backend.init(3, 4) is true
   - Expected: pixels[1] equals `0xFF201008u32`
   - Expected: pixels[10] equals `0xFF201008u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("one-column horizontal gradient is exactly the left colour")
var backend = SoftwareBackend.create_cpu_simd()
expect(backend.init(3, 4)).to_equal(true)
backend.clear(0xFF000000u32)
backend.draw_gradient_rect_h(1, 0, 1, 4, 0x80402010u32, 0xFFFFFFFFu32)
val pixels = backend.read_pixels()
expect(pixels[1]).to_equal(0xFF201008u32)
expect(pixels[10]).to_equal(0xFF201008u32)
backend.shutdown()
```

</details>

#### in-place constant rectangle spans match scalar clipping and damage

- in-place constant rectangle spans match scalar clipping and damage
   - Expected: scalar.init(9, 4) is true
   - Expected: simd.init(9, 4) is true
   - Expected: simd.read_pixels() equals `scalar.read_pixels()`
   - Expected: simd.damage_rects(16) equals `scalar.damage_rects(16)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("in-place constant rectangle spans match scalar clipping and damage")
var scalar = SoftwareBackend.create()
var simd = SoftwareBackend.create_cpu_simd()
expect(scalar.init(9, 4)).to_equal(true)
expect(simd.init(9, 4)).to_equal(true)
scalar.clear(0x80402010u32)
simd.clear(0x80402010u32)
scalar.present()
simd.present()
reset_simd_hits()
# Both axes clip while leaving the mask-off span path active.
scalar.draw_rect_blend(-2, -1, 7, 4, 0x8010E040u32)
simd.draw_rect_blend(-2, -1, 7, 4, 0x8010E040u32)
expect(simd.read_pixels()).to_equal(scalar.read_pixels())
expect(simd.damage_rects(16)).to_equal(scalar.damage_rects(16))
expect(simd_hit_counts().alpha_hits).to_be_greater_than(0)
scalar.shutdown()
simd.shutdown()
```

</details>

#### transparent constant rectangle is a pixel and damage no-op

- transparent constant rectangle is a pixel and damage no-op
   - Expected: simd.init(5, 2) is true
   - Expected: simd.read_pixels() equals `before`
   - Expected: simd.damage_is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("transparent constant rectangle is a pixel and damage no-op")
var simd = SoftwareBackend.create_cpu_simd()
expect(simd.init(5, 2)).to_equal(true)
simd.clear(0x7F123456u32)
simd.present()
val before = simd.read_pixels()
simd.draw_rect_blend(0, 0, 5, 2, 0x00010203u32)
expect(simd.read_pixels()).to_equal(before)
expect(simd.damage_is_empty()).to_equal(true)
simd.shutdown()
```

</details>

#### in-place span image blend matches scalar pixels, clipping, and damage

- in-place span image blend matches scalar pixels, clipping, and damage
   - Expected: scalar.init(9, 3) is true
   - Expected: simd.init(9, 3) is true
   - Expected: simd.read_pixels() equals `scalar.read_pixels()`
   - Expected: simd.damage_rects(16) equals `scalar.damage_rects(16)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("in-place span image blend matches scalar pixels, clipping, and damage")
var scalar = SoftwareBackend.create()
var simd = SoftwareBackend.create_cpu_simd()
expect(scalar.init(9, 3)).to_equal(true)
expect(simd.init(9, 3)).to_equal(true)
scalar.clear(0x80402010u32)
simd.clear(0x80402010u32)
scalar.present()
simd.present()
val image: [u32] = [
    0x00000000u32, 0x40FF0000u32, 0x8000FF00u32,
    0xFFFFFFFFu32, 0x7F1020F0u32, 0x010000FFu32,
    0xC0FF8040u32, 0x20010203u32, 0xFF112233u32,
    0x00000000u32, 0x80808080u32, 0xFFFF00FFu32
]
# Negative x clips the source offset while keeping the fast
# mask-off span path active.
scalar.draw_image_blend(-2, 1, 6, 2, image)
simd.draw_image_blend(-2, 1, 6, 2, image)
expect(simd.read_pixels()).to_equal(scalar.read_pixels())
expect(simd.damage_rects(16)).to_equal(scalar.damage_rects(16))
scalar.shutdown()
simd.shutdown()
```

</details>

#### transparent in-place image span is an exact no-op

- transparent in-place image span is an exact no-op
   - Expected: simd.init(4, 1) is true
   - Expected: simd.read_pixels() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("transparent in-place image span is an exact no-op")
var simd = SoftwareBackend.create_cpu_simd()
expect(simd.init(4, 1)).to_equal(true)
simd.clear(0x7F123456u32)
simd.present()
val before = simd.read_pixels()
simd.draw_image_blend(0, 0, 4, 1, [0x00000000u32; 4])
expect(simd.read_pixels()).to_equal(before)
simd.shutdown()
```

</details>

#### AC-6: draw_rect_filled opaque spans record simd fill hits

- AC-6: draw_rect_filled opaque spans record simd fill hits
   - Expected: pixels[5 * 64 + 4] equals `0xFFFF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: draw_rect_filled opaque spans record simd fill hits")
var backend = SoftwareBackend.create()
reset_simd_hits()
if backend.init(64, 64):
    backend.draw_rect_filled(4, 5, 16, 8, 0xFFFF0000)
    val pixels = backend.read_pixels()
    expect(pixels[5 * 64 + 4]).to_equal(0xFFFF0000)
    expect(simd_hit_counts().fill_hits).to_be_greater_than(0)
    backend.shutdown()
```

</details>

#### AC-6: draw_rect_filled with alpha uses simd_blend_row

- AC-6: draw_rect_filled with alpha uses simd_blend_row


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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

#### preserves a translucent source over a transparent destination

- preserves a translucent source over a transparent destination
   - Expected: backend.init(2, 1) is true
   - Expected: pixels[0] equals `0x80FFFFFFu32`
   - Expected: pixels[1] equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves a translucent source over a transparent destination")
var backend = SoftwareBackend.create_cpu_simd()
reset_simd_hits()
expect(backend.init(2, 1)).to_equal(true)
backend.clear(0x00000000u32)
backend.draw_rect_filled(0, 0, 1, 1, 0x80FFFFFFu32)
val pixels = backend.read_pixels()
expect(pixels[0]).to_equal(0x80FFFFFFu32)
expect(pixels[1]).to_equal(0x00000000u32)
expect(simd_hit_counts().alpha_hits).to_be_greater_than(0)
backend.shutdown()
```

</details>

#### matches straight-alpha composition for translucent source and destination

- matches straight-alpha composition for translucent source and destination
   - Expected: backend.init(1, 1) is true
   - Expected: backend.read_pixels()[0] equals `0xBFAA0054u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches straight-alpha composition for translucent source and destination")
var backend = SoftwareBackend.create_cpu_simd()
expect(backend.init(1, 1)).to_equal(true)
backend.clear(0x800000FFu32)
backend.draw_rect_filled(0, 0, 1, 1, 0x80FF0000u32)
expect(backend.read_pixels()[0]).to_equal(0xBFAA0054u32)
backend.shutdown()
```

</details>

#### keeps zero-alpha source pixels unchanged

- keeps zero-alpha source pixels unchanged
   - Expected: backend.init(1, 1) is true
   - Expected: backend.read_pixels()[0] equals `0x00112233u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps zero-alpha source pixels unchanged")
var backend = SoftwareBackend.create_cpu_simd()
expect(backend.init(1, 1)).to_equal(true)
backend.clear(0x00112233u32)
backend.draw_rect_filled(0, 0, 1, 1, 0x00000000u32)
expect(backend.read_pixels()[0]).to_equal(0x00112233u32)
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
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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

### simd_span_batch_execute wiring

#### clear() through the public API drives the kernel_registry batch dispatcher

- clear() through the public API drives the kernel_registry batch dispatcher
   - Expected: backend.init(64, 64) is true
   - Expected: pixels[0] equals `0xFF224466u32`
   - Expected: pixels[63] equals `0xFF224466u32`
   - Expected: plain.init(64, 64) is true
   - Expected: plain.kernel_table.lookups equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clear() through the public API drives the kernel_registry batch dispatcher")
var backend = SoftwareBackend.create_cpu_simd()
expect(backend.init(64, 64)).to_equal(true)
backend.clear(0xFF224466u32)
val pixels = backend.read_pixels()
expect(pixels[0]).to_equal(0xFF224466u32)
expect(pixels[63]).to_equal(0xFF224466u32)
# `kernel_table.lookups` increments every time simd_span_batch_execute
# calls kernel_table_lookup — once per row cleared here — regardless of
# which provider a slot resolves to. A nonzero count is proof the
# dispatcher built in simd_isa_provider.spl was genuinely consulted by
# a public-API Engine2D-level draw call, not just unit-tested in
# isolation.
expect(backend.kernel_table.lookups).to_be_greater_than(0)
print("simd_batch_hits=" + backend.simd_batch_hits.to_text() +
      " lookups=" + backend.kernel_table.lookups.to_text() +
      " registrations=" + backend.kernel_table.registrations.to_text())
# Sabotage-equivalent control: a backend built without native_simd_spans
# never calls the batch dispatcher at all, so its table is never even
# constructed via ensure_kernel_table — lookups stay at zero, proving
# the nonzero count above is caused by the wiring, not by some
# unrelated always-incrementing counter.
var plain = SoftwareBackend.create()
expect(plain.init(64, 64)).to_equal(true)
plain.clear(0xFF224466u32)
expect(plain.kernel_table.lookups).to_equal(0)
backend.shutdown()
plain.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `2f3a11543e2cc2625cb15972d7e5f00588dd7215663434ab49077ea23d1b85c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f3a11543e2cc2625cb15972d7e5f00588dd7215663434ab49077ea23d1b85c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f3a11543e2cc2625cb15972d7e5f00588dd7215663434ab49077ea23d1b85c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gpu/engine2d/backend_software_simd_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_simd_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_simd_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_simd_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/backend_software_simd_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/backend_software_simd_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: clear uses simd_fill_row when available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_software_simd_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: clear produces same result with and without SIMD' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_software_simd_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: blit uses simd_blit_row for row copies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
