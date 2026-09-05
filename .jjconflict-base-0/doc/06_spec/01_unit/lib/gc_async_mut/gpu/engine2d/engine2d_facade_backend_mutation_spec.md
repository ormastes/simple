# Engine2D Facade Backend Mutation Specification

> Verifies that the public Engine2D facade delegates clear, filled-rectangle, image blits, clip/mask state, present, and readback through requested software and CPU SIMD backends.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Facade Backend Mutation Specification

Verifies that the public Engine2D facade delegates clear, filled-rectangle, image blits, clip/mask state, present, and readback through requested software and CPU SIMD backends.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md |
| Design | doc/04_architecture/ui/engine_2d.md |
| Research | doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the public Engine2D facade delegates clear, filled-rectangle,
image blits, clip/mask state, present, and readback through requested software
and CPU SIMD backends.

This closes the local, non-platform-specific half of the Engine2D facade
mutation feature request: the production facade must preserve backend pixel
mutations instead of callers reaching into concrete backend implementations.

The scenarios render a reduced 16x16 scene through
`Engine2D.create_with_backend`, read the final framebuffer through
`Engine2D.read_pixels`, and assert concrete pixel values at clear, inside-rect,
and outside-rect coordinates. The CPU SIMD scenario also proves the facade path
reaches the SIMD fill provider by checking the fill hit counter.

## Evidence Model

The spec intentionally avoids direct `SoftwareBackend` or `CpuBackend` calls.
All rendering commands go through `Engine2D.clear`,
`Engine2D.draw_rect_filled`, `Engine2D.draw_image`,
`Engine2D.draw_image_scaled`, `Engine2D.draw_image_transform`,
`Engine2D.set_clip`, `Engine2D.set_mask`, `Engine2D.present`, and
`Engine2D.read_pixels`.

**Requirements:** N/A

**Plan:** doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md

**Design:** doc/04_architecture/ui/engine_2d.md

**Research:** doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md

## Syntax

Use `std.spec` examples with built-in matchers only. Pixel assertions compare
exact framebuffer values; the SIMD scenario uses `to_be_greater_than(0)` for
the recorded fill hit count.

## Scenarios

### Engine2D facade backend mutation

#### software blend-mode rectangles match the emulation oracle for every mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- software blend-mode rectangles match the emulation oracle for every mode
   - Expected: direct.init(7, 4) is true
   - Expected: oracle.init(7, 4) is true
   - Expected: direct.read_pixels() equals `oracle.read_pixels()`
   - Expected: direct.damage_rects(16) equals `oracle.damage_rects(16)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software blend-mode rectangles match the emulation oracle for every mode")
var mode = 0
while mode <= 5:
    var direct = SoftwareBackend.create()
    var oracle = SoftwareBackend.create()
    expect(direct.init(7, 4)).to_equal(true)
    expect(oracle.init(7, 4)).to_equal(true)
    var seed: [u32] = [0u32; 28]
    var i = 0
    while i < seed.len():
        seed[i] = 0x40201008u32 + ((i as u32) * 0x0003070Bu32)
        i = i + 1
    direct.draw_image(0, 0, 7, 4, seed)
    oracle.draw_image(0, 0, 7, 4, seed)
    direct.present()
    oracle.present()
    direct.draw_rect_blend_mode(-2, 1, 7, 4, 0x80D05020u32, mode)
    emu_draw_rect_blend_mode(oracle, -2, 1, 7, 4, 0x80D05020u32, mode)
    expect(direct.read_pixels()).to_equal(oracle.read_pixels())
    expect(direct.damage_rects(16)).to_equal(oracle.damage_rects(16))
    direct.shutdown()
    oracle.shutdown()
    mode = mode + 1
```

</details>

#### software blend-mode rectangle preserves clip mask and zero-alpha damage

- software blend-mode rectangle preserves clip mask and zero-alpha damage
   - Expected: direct.init(6, 4) is true
   - Expected: oracle.init(6, 4) is true
   - Expected: direct.read_pixels() equals `oracle.read_pixels()`
   - Expected: direct.damage_rects(16) equals `oracle.damage_rects(16)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software blend-mode rectangle preserves clip mask and zero-alpha damage")
var direct = SoftwareBackend.create()
var oracle = SoftwareBackend.create()
expect(direct.init(6, 4)).to_equal(true)
expect(oracle.init(6, 4)).to_equal(true)
direct.clear(0x60402010u32)
oracle.clear(0x60402010u32)
direct.present()
oracle.present()
var mask: [u8] = [0u8; 24]
var i = 0
while i < mask.len():
    if (i % 2) == 0: mask[i] = 255u8
    i = i + 1
direct.set_clip(1, 1, 4, 2)
oracle.set_clip(1, 1, 4, 2)
direct.set_mask(mask, 6, 4)
oracle.set_mask(mask, 6, 4)
direct.draw_rect_blend_mode(0, 0, 6, 4, 0x00D05020u32, 3)
emu_draw_rect_blend_mode(oracle, 0, 0, 6, 4, 0x00D05020u32, 3)
expect(direct.read_pixels()).to_equal(oracle.read_pixels())
expect(direct.damage_rects(16)).to_equal(oracle.damage_rects(16))
direct.shutdown()
oracle.shutdown()
```

</details>

#### software scaled image snapshots an aliased framebuffer source

- software scaled image snapshots an aliased framebuffer source
   - Expected: backend.init(3, 2) is true
   - Expected: backend.read_pixels() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software scaled image snapshots an aliased framebuffer source")
var backend = SoftwareBackend.create()
expect(backend.init(3, 2)).to_equal(true)
backend.buf = [
    0xFF010203u32, 0xFF111213u32, 0xFF212223u32,
    0xFF313233u32, 0xFF414243u32, 0xFF515253u32
]
backend.draw_image_scaled(0, 0, 3, 2, 6, 1, backend.buf)
expect(backend.read_pixels()).to_equal([
    0xFF010203u32, 0xFF212223u32, 0xFF414243u32,
    0xFF010203u32, 0xFF212223u32, 0xFF414243u32
])
backend.shutdown()
```

</details>

#### software backend preserves clear and filled rectangle pixels

- software backend preserves clear and filled rectangle pixels
   - Expected: pixels.len() equals `WIDTH * HEIGHT`
   - Expected: pixels[0] equals `BG`
   - Expected: pixels[5 * WIDTH + 4] equals `FG`
   - Expected: pixels[8 * WIDTH + 9] equals `FG`
   - Expected: pixels[8 * WIDTH + 10] equals `BG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software backend preserves clear and filled rectangle pixels")
val pixels = render_facade_pixels("software")

expect(pixels.len()).to_equal(WIDTH * HEIGHT)
expect(pixels[0]).to_equal(BG)
expect(pixels[5 * WIDTH + 4]).to_equal(FG)
expect(pixels[8 * WIDTH + 9]).to_equal(FG)
expect(pixels[8 * WIDTH + 10]).to_equal(BG)
```

</details>

#### software backend draw_image honors facade clip and mask state

- software backend draw_image honors facade clip and mask state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software backend draw_image honors facade clip and mask state")
expect_draw_image_clip_mask("software")
```

</details>

#### software backend draw_image_scaled honors facade clip and mask state

- software backend draw_image_scaled honors facade clip and mask state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software backend draw_image_scaled honors facade clip and mask state")
expect_draw_image_scaled_clip_mask("software")
```

</details>

#### software backend draw_image_transform honors facade clip and mask state

- software backend draw_image_transform honors facade clip and mask state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("software backend draw_image_transform honors facade clip and mask state")
expect_draw_image_transform_clip_mask("software")
```

</details>

#### cpu_simd backend preserves pixels and records SIMD fill use

- cpu_simd backend preserves pixels and records SIMD fill use
   - Expected: pixels.len() equals `WIDTH * HEIGHT`
   - Expected: pixels[0] equals `BG`
   - Expected: pixels[5 * WIDTH + 4] equals `FG`
   - Expected: pixels[8 * WIDTH + 9] equals `FG`
   - Expected: pixels[8 * WIDTH + 10] equals `BG`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cpu_simd backend preserves pixels and records SIMD fill use")
reset_simd_hits()
val pixels = render_facade_pixels("cpu_simd")

expect(pixels.len()).to_equal(WIDTH * HEIGHT)
expect(pixels[0]).to_equal(BG)
expect(pixels[5 * WIDTH + 4]).to_equal(FG)
expect(pixels[8 * WIDTH + 9]).to_equal(FG)
expect(pixels[8 * WIDTH + 10]).to_equal(BG)
expect(simd_hit_counts().fill_hits).to_be_greater_than(0)
```

</details>

#### cpu_simd backend draw_image honors facade clip and mask state

- cpu_simd backend draw_image honors facade clip and mask state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cpu_simd backend draw_image honors facade clip and mask state")
expect_draw_image_clip_mask("cpu_simd")
```

</details>

#### cpu_simd backend draw_image_scaled honors facade clip and mask state

- cpu_simd backend draw_image_scaled honors facade clip and mask state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cpu_simd backend draw_image_scaled honors facade clip and mask state")
expect_draw_image_scaled_clip_mask("cpu_simd")
```

</details>

#### cpu_simd backend draw_image_transform honors facade clip and mask state

- cpu_simd backend draw_image_transform honors facade clip and mask state


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cpu_simd backend draw_image_transform honors facade clip and mask state")
expect_draw_image_transform_clip_mask("cpu_simd")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/08_tracking/feature/engine2d_trait_facade_backend_execution_2026-06-02.md`
- **Design:** `doc/04_architecture/ui/engine_2d.md`
- **Research:** `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e775634039a57de60edf20c80e67035c2a493274ca2bbbc1b21abe3dd073efe6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e775634039a57de60edf20c80e67035c2a493274ca2bbbc1b21abe3dd073efe6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e775634039a57de60edf20c80e67035c2a493274ca2bbbc1b21abe3dd073efe6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'software blend-mode rectangles match the emulation oracle for every mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.spl:193:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'software blend-mode rectangle preserves clip mask and zero-alpha damage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.spl:220:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'software scaled image snapshots an aliased framebuffer source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
