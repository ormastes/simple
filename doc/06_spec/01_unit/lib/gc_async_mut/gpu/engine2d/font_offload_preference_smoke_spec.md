# Font Offload Preference Smoke Specification

> Tests covering Engine2D font offload preference smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Font Offload Preference Smoke Specification

## Scenarios

### Engine2D font offload preference smoke

#### replays unsupported and current font programs from quad zero after GPU refusal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- replays unsupported and current font programs from quad zero after GPU refusal
   - Expected: engine._draw_font_batch(0, 0, _one_pixel_batch(2, 0xff123456u32)) is true
   - Expected: engine.read_pixels()[4] equals `0xff123456u32`
   - Expected: engine._draw_font_batch(0, 0, _one_pixel_batch(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, 0xffabcdefu32)) is true
   - Expected: engine.read_pixels()[4] equals `0xffabcdefu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replays unsupported and current font programs from quad zero after GPU refusal")
var engine = Engine2D.create_with_backend(3, 2, "software")
engine.cuda_backend = CudaBackend.create()

engine.clear(0xff000000u32)
expect(engine._draw_font_batch(0, 0, _one_pixel_batch(2, 0xff123456u32))).to_equal(true)
expect(engine.read_pixels()[4]).to_equal(0xff123456u32)

engine.clear(0xff000000u32)
expect(engine._draw_font_batch(0, 0, _one_pixel_batch(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, 0xffabcdefu32))).to_equal(true)
expect(engine.read_pixels()[4]).to_equal(0xffabcdefu32)
engine.shutdown()
```

</details>

#### replays a failed ROCm font batch from quad zero on CPU

- replays a failed ROCm font batch from quad zero on CPU
   - Expected: engine._draw_font_batch_plan(0, 0, _one_pixel_batch(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, 0xff2468acu32), ["rocm", "cpu"]) is true
   - Expected: engine.font_execution_attempts() equals `["rocm:failed", "cpu:success"]`
   - Expected: engine.font_execution_target() equals `cpu`
   - Expected: engine.read_pixels()[4] equals `0xff2468acu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replays a failed ROCm font batch from quad zero on CPU")
var engine = Engine2D.create_with_backend(3, 2, "software")
engine.rocm_backend = RocmBackend.create()
engine.clear(0xff000000u32)

expect(engine._draw_font_batch_plan(0, 0, _one_pixel_batch(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, 0xff2468acu32), ["rocm", "cpu"])).to_equal(true)
expect(engine.font_execution_attempts()).to_equal(["rocm:failed", "cpu:success"])
expect(engine.font_execution_target()).to_equal("cpu")
expect(engine.read_pixels()[4]).to_equal(0xff2468acu32)
engine.shutdown()
```

</details>

#### replays only the unsubmitted suffix from prefix one

- replays only the unsubmitted suffix from prefix one
   - Expected: engine._draw_font_batch_cpu_suffix(0, 0, batch, 1) equals `2`
   - Expected: pixels[0] equals `0xff000000u32`
   - Expected: pixels[1] equals `0xff445566u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replays only the unsubmitted suffix from prefix one")
var engine = Engine2D.create_with_backend(2, 1, "software")
engine.clear(0xff000000u32)
val batch = _two_pixel_batch()
expect(engine._draw_font_batch_cpu_suffix(0, 0, batch, 1)).to_equal(2)
val pixels = engine.read_pixels()
expect(pixels[0]).to_equal(0xff000000u32)
expect(pixels[1]).to_equal(0xff445566u32)
engine.shutdown()
```

</details>

#### uses the shared font offload order for vector and bitmap evidence

- uses the shared font offload order for vector and bitmap evidence
   - Expected: vector.backend_name equals `rocm`
   - Expected: vector.generated.backend_name equals `rocm`
   - Expected: vector.production_ready is false
   - Expected: bitmap.backend_name equals `rocm`
   - Expected: bitmap.glyph_raster_generated.backend_name equals `rocm`
   - Expected: bitmap.gpu_glyph_raster_plan_ready is true
   - Expected: bitmap.production_ready is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses the shared font offload order for vector and bitmap evidence")
val vector = vector_font_preferred_offload_evidence(
    ["vulkan", "amd-hip", "cpu"],
    32,
    16,
    true,
    true,
    4096,
    _accelerator(0, 0, "vector-glyph-readback-required")
)
val bitmap = bitmap_font_preferred_offload_evidence(
    ["vulkan", "amd-hip", "cpu"],
    32,
    16,
    true,
    true,
    4096
)

expect(vector.backend_name).to_equal("rocm")
expect(vector.generated.backend_name).to_equal("rocm")
expect(vector.production_ready).to_equal(false)
expect(bitmap.backend_name).to_equal("rocm")
expect(bitmap.glyph_raster_generated.backend_name).to_equal("rocm")
expect(bitmap.gpu_glyph_raster_plan_ready).to_equal(true)
expect(bitmap.production_ready).to_equal(false)
```

</details>

#### requires readback checksum evidence before font offload is production ready

- requires readback checksum evidence before font offload is production ready
   - Expected: vector.backend_name equals `rocm`
   - Expected: vector.execution.expected_checksum equals `vector_checksum`
   - Expected: vector.execution.actual_checksum equals `vector_checksum`
   - Expected: vector.production_ready is true
   - Expected: bitmap.backend_name equals `rocm`
   - Expected: bitmap.execution.expected_checksum equals `bitmap_checksum`
   - Expected: bitmap.execution.actual_checksum equals `bitmap_checksum`
   - Expected: bitmap.production_ready is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires readback checksum evidence before font offload is production ready")
val vector_pixels = [0u8, 9u8, 255u8, 3u8]
val vector_checksum = vector_font_glyph_pixels_checksum(vector_pixels)
val vector = vector_font_preferred_glyph_readback_evidence(
    ["vulkan", "amd-hip", "cpu"],
    4,
    1,
    4096,
    7,
    11,
    true,
    true,
    true,
    _accelerator(1, 4, "rocm-vector-font-glyph-pixels-returned"),
    vector_pixels,
    vector_checksum
)
val glyph_bits = [1u32, 0u32, 3u32, 0u32]
val bitmap_checksum = bitmap_glyph_raster_mask_checksum(glyph_bits, 2, 2, 0xff224466u32)
val bitmap = bitmap_glyph_raster_preferred_mask_readback_evidence(
    ["vulkan", "amd-hip", "cpu"],
    glyph_bits,
    2,
    2,
    0xff224466u32,
    4096,
    7,
    11,
    true,
    true,
    true,
    bitmap_checksum
)

expect(vector.backend_name).to_equal("rocm")
expect(vector.execution.expected_checksum).to_equal(vector_checksum)
expect(vector.execution.actual_checksum).to_equal(vector_checksum)
expect(vector.production_ready).to_equal(true)
expect(bitmap.backend_name).to_equal("rocm")
expect(bitmap.execution.expected_checksum).to_equal(bitmap_checksum)
expect(bitmap.execution.actual_checksum).to_equal(bitmap_checksum)
expect(bitmap.production_ready).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/font_offload_preference_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D font offload preference smoke.
- Engine2D font offload preference smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `95b145b95feda0ffe86229360764d33158fe7d99619187ef88bcfb3b73143464`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95b145b95feda0ffe86229360764d33158fe7d99619187ef88bcfb3b73143464`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95b145b95feda0ffe86229360764d33158fe7d99619187ef88bcfb3b73143464`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/font_offload_preference_smoke_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/font_offload_preference_smoke_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/font_offload_preference_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/font_offload_preference_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/font_offload_preference_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/font_offload_preference_smoke_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replays unsupported and current font programs from quad zero after GPU refusal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/font_offload_preference_smoke_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replays a failed ROCm font batch from quad zero on CPU' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/font_offload_preference_smoke_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replays only the unsubmitted suffix from prefix one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
