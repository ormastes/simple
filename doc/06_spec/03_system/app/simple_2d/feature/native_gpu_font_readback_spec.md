# Native GPU Font Readback

> Verifies the native gpu font readback behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native GPU Font Readback

Verifies the native gpu font readback behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the native gpu font readback behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### native GPU font promotion evidence

#### should reject missing or noncanonical SimpleOS artifact provenance

- Verify: should reject missing or noncanonical SimpleOS artifact provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-011 REQ-012 REQ-013
step("Verify: should reject missing or noncanonical SimpleOS artifact provenance")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(_simpleos_artifact_metadata_valid("")).to_be(false)
val copied = _simpleos_canonical_artifact_record().replace(
    SIMPLEOS_WRAPPER_PATH, "/tmp/copied-simpleos-evidence.shs")
expect(_simpleos_artifact_metadata_valid(copied)).to_be(false)
```

</details>

#### should reject malformed or ambiguous SimpleOS artifact hashes

- Verify: should reject malformed or ambiguous SimpleOS artifact hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-011 REQ-012 REQ-013
step("Verify: should reject malformed or ambiguous SimpleOS artifact hashes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val uppercase = _simpleos_canonical_artifact_record().replace(
    SIMPLEOS_ZERO_SHA256, "A000000000000000000000000000000000000000000000000000000000000000")
expect(_simpleos_artifact_metadata_valid(uppercase)).to_be(false)
val duplicate = _simpleos_canonical_artifact_record() +
    "simpleos_wm_fullscreen_wrapper_sha256={SIMPLEOS_ZERO_SHA256}\n"
expect(_simpleos_artifact_metadata_valid(duplicate)).to_be(false)
val empty_first = "simpleos_wm_fullscreen_wrapper_sha256=\n" +
    _simpleos_canonical_artifact_record()
expect(_simpleos_artifact_metadata_valid(empty_first)).to_be(false)
```

</details>

#### should reject copied env-only SimpleOS artifact evidence

- Verify: should reject copied env-only SimpleOS artifact evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-011 REQ-012 REQ-014
step("Verify: should reject copied env-only SimpleOS artifact evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val copied_record = _simpleos_canonical_artifact_record()
expect(_simpleos_artifact_metadata_valid(copied_record)).to_be(true)
expect(_simpleos_artifact_files_valid(copied_record)).to_be(false)
```

</details>

#### should classify controlled missing native graphics hardware as unavailable

- Verify: should classify controlled missing native graphics hardware as unavailable
- Prove native submission and device readback
   - Expected: classify_native_font_promotion(unavailable_2d, unavailable_3d) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-011 REQ-012 REQ-014
step("Verify: should classify controlled missing native graphics hardware as unavailable")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prove native submission and device readback")
val unavailable_2d = _engine2d_unavailable("controlled-device-unavailable")
val unavailable_3d = _engine3d_unavailable("controlled-device-unavailable")
expect(classify_native_font_promotion(unavailable_2d, unavailable_3d)).to_equal("unavailable")
expect(expect_engine2d_font_readback(unavailable_2d)).to_be(false)
expect(expect_engine3d_font_readback(unavailable_3d)).to_be(false)
```

</details>

#### should reject forged pass labels without native device proof

- Verify: should reject forged pass labels without native device proof
- Prove native submission and device readback
   - Expected: classify_native_font_promotion(forged_2d, forged_3d) equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-011 REQ-012 REQ-013 REQ-014
step("Verify: should reject forged pass labels without native device proof")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prove native submission and device readback")
val forged_2d = Engine2DFontReadbackEvidence(
    status: "pass", reason: "forged", device_identity: 1,
    device_name: "forged-device", device_type: "virtual",
    driver_identity: "forged-driver", pipeline_handle: 1, atlas_handle: 1,
    command_handle: 1, fence_handle: 1, fence_waited: true,
    fence_destroyed: true, readback_source: "cpu_fallback",
    readback_handle: 1, readback_bytes: 16384, execution_target: "vulkan",
    nonblank_pixels: true, cpu_oracle_parity: true)
val forged_3d = Engine3DFontReadbackEvidence(
    status: "pass", reason: "forged", device_handle: 1,
    device_name: "forged-device", device_type: "virtual",
    driver_identity: "forged-driver", submitted_command_handle: 1,
    pipeline_handle: 1, world_pipeline_handle: 2, texture_handle: 1,
    texture_binding_ready: true, atlas_owner_identity: "forged-owner",
    atlas_generation: 1, atlas_payload_sha256: FONT_ASSET_SHA256,
    sampler_handle: 1, hud_draws: 1, hud_placement_verified: true,
    world_draws: 1, world_depth_transform_verified: true,
    fence_handle: 1, fence_waited: true, fence_destroyed: true,
    readback_source: "device_image_readback", color_image_handle: 1,
    readback_bytes: 16384, readback_matches_evidence: false,
    nonblank_pixels: true, cpu_oracle_parity: true,
    translucent_destination_parity: false)
expect(classify_native_font_promotion(forged_2d, forged_3d)).to_equal("rejected")
expect(expect_engine2d_font_readback(forged_2d)).to_be(false)
expect(expect_engine3d_font_readback(forged_3d)).to_be(false)
```

</details>

#### should promote Engine2D and Engine3D fonts with a consistent Vulkan device tuple

- Verify: should promote Engine2D and Engine3D fonts with a consistent Vulkan device tuple
- Prove native submission and device readback
- Render Engine2D text on the promoted backend
- Render Engine3D HUD and world text on the promoted backend
   - Expected: promotion equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-011 REQ-012 REQ-013 REQ-014
step("Verify: should promote Engine2D and Engine3D fonts with a consistent Vulkan device tuple")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prove native submission and device readback")
step("Render Engine2D text on the promoted backend")
step("Render Engine3D HUD and world text on the promoted backend")
val engine2d = _collect_engine2d_font_readback()
val engine3d = _collect_engine3d_font_readback()
val promotion = classify_native_font_promotion(engine2d, engine3d)
print "engine2d_font status={engine2d.status} reason={engine2d.reason} device={engine2d.device_identity} pipeline={engine2d.pipeline_handle} atlas={engine2d.atlas_handle} fence={engine2d.fence_handle} readback_bytes={engine2d.readback_bytes}"
print "engine3d_font status={engine3d.status} reason={engine3d.reason} device={engine3d.device_handle} hud_pipeline={engine3d.pipeline_handle} world_pipeline={engine3d.world_pipeline_handle} texture={engine3d.texture_handle} atlas_owner={engine3d.atlas_owner_identity} atlas_generation={engine3d.atlas_generation} atlas_sha256={engine3d.atlas_payload_sha256} sampler={engine3d.sampler_handle} fence={engine3d.fence_handle} readback_bytes={engine3d.readback_bytes} translucent_destination_parity={engine3d.translucent_destination_parity}"
if promotion != "pass":
    fail_test("native font promotion " + promotion + ": Engine2D=" +
        engine2d.reason + " Engine3D=" + engine3d.reason)
expect(expect_engine2d_font_readback(engine2d)).to_be(true)
expect(expect_engine3d_font_readback(engine3d)).to_be(true)
expect(promotion).to_equal("pass")
```

</details>

#### should capture the pinned SimpleOS glyph from guest framebuffer memory

- Verify: should capture the pinned SimpleOS glyph from guest framebuffer memory
- Boot SimpleOS with the pinned font asset
- Capture SimpleOS pinned-font pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-011 REQ-012 REQ-013 REQ-014
step("Verify: should capture the pinned SimpleOS glyph from guest framebuffer memory")
step("Boot SimpleOS with the pinned font asset")
step("Capture SimpleOS pinned-font pixels")
val evidence = _collect_simpleos_pixel_evidence()
if not expect_simpleos_font_pixel_oracle(evidence):
    fail_test("SimpleOS pinned-font pixel oracle unavailable: " + evidence.reason)
expect(expect_simpleos_font_pixel_oracle(evidence)).to_be(true)
```

</details>

#### should meet warm latency, recovery, GPU benefit, upload, RSS, and resource budgets

- Verify: should meet warm latency, recovery, GPU benefit, upload, RSS, and resource budgets
- Measure warm font rendering and resource bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-011 REQ-012 REQ-013 REQ-014
step("Verify: should meet warm latency, recovery, GPU benefit, upload, RSS, and resource budgets")
step("Measure warm font rendering and resource bounds")
val evidence = read_font_perf_evidence()
if not expect_font_perf_budget(evidence):
    fail_test("native font performance evidence unavailable: " + evidence.reason)
expect(expect_font_perf_budget(evidence)).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e34482fe0a34299ef56c6daeda5758d5badc528ecdf71c827648ab128c7cd10d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e34482fe0a34299ef56c6daeda5758d5badc528ecdf71c827648ab128c7cd10d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e34482fe0a34299ef56c6daeda5758d5badc528ecdf71c827648ab128c7cd10d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:526:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing or noncanonical SimpleOS artifact provenance' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:536:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed or ambiguous SimpleOS artifact hashes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:551:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject copied env-only SimpleOS artifact evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:560:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify controlled missing native graphics hardware as unavailable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:572:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject forged pass labels without native device proof' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:603:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should promote Engine2D and Engine3D fonts with a consistent Vulkan device tuple' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
