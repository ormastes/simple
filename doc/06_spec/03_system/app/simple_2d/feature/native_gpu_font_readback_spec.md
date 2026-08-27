# Native GPU Font Readback

> Release-blocking native evidence for Engine2D and Engine3D font texture

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native GPU Font Readback

Release-blocking native evidence for Engine2D and Engine3D font texture

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Release-blocking native evidence for Engine2D and Engine3D font texture
rendering, SimpleOS pinned-font pixels, and warm performance/resource bounds. Unavailable hardware
and missing durable artifacts fail explicitly; CPU rendering and uploaded-only
textures cannot satisfy this spec.

## Scenarios

### native GPU font promotion evidence

#### should reject missing or noncanonical SimpleOS artifact provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject missing or noncanonical SimpleOS artifact provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing or noncanonical SimpleOS artifact provenance")
expect(_simpleos_artifact_metadata_valid("")).to_be(false)
val copied = _simpleos_canonical_artifact_record().replace(
    SIMPLEOS_WRAPPER_PATH, "/tmp/copied-simpleos-evidence.shs")
expect(_simpleos_artifact_metadata_valid(copied)).to_be(false)
```

</details>

#### should reject malformed or ambiguous SimpleOS artifact hashes

- should reject malformed or ambiguous SimpleOS artifact hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject malformed or ambiguous SimpleOS artifact hashes")
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

- should reject copied env-only SimpleOS artifact evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject copied env-only SimpleOS artifact evidence")
val copied_record = _simpleos_canonical_artifact_record()
expect(_simpleos_artifact_metadata_valid(copied_record)).to_be(true)
expect(_simpleos_artifact_files_valid(copied_record)).to_be(false)
```

</details>

#### should classify controlled missing native graphics hardware as unavailable

- should classify controlled missing native graphics hardware as unavailable
- Prove native submission and device readback
   - Expected: classify_native_font_promotion(unavailable_2d, unavailable_3d) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify controlled missing native graphics hardware as unavailable")
step("Prove native submission and device readback")
val unavailable_2d = _engine2d_unavailable("controlled-device-unavailable")
val unavailable_3d = _engine3d_unavailable("controlled-device-unavailable")
expect(classify_native_font_promotion(unavailable_2d, unavailable_3d)).to_equal("unavailable")
expect(expect_engine2d_font_readback(unavailable_2d)).to_be(false)
expect(expect_engine3d_font_readback(unavailable_3d)).to_be(false)
```

</details>

#### should reject forged pass labels without native device proof

- should reject forged pass labels without native device proof
- Prove native submission and device readback
   - Expected: classify_native_font_promotion(forged_2d, forged_3d) equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject forged pass labels without native device proof")
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

- should promote Engine2D and Engine3D fonts with a consistent Vulkan device tuple
- Prove native submission and device readback
- Render Engine2D text on the promoted backend
- Render Engine3D HUD and world text on the promoted backend
   - Expected: promotion equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should promote Engine2D and Engine3D fonts with a consistent Vulkan device tuple")
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

- should capture the pinned SimpleOS glyph from guest framebuffer memory
- Boot SimpleOS with the pinned font asset
- Capture SimpleOS pinned-font pixels
- fail test


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should capture the pinned SimpleOS glyph from guest framebuffer memory")
step("Boot SimpleOS with the pinned font asset")
step("Capture SimpleOS pinned-font pixels")
val evidence = _collect_simpleos_pixel_evidence()
if not expect_simpleos_font_pixel_oracle(evidence):
    fail_test("SimpleOS pinned-font pixel oracle unavailable: " + evidence.reason)
expect(expect_simpleos_font_pixel_oracle(evidence)).to_be(true)
```

</details>

#### should meet warm latency, recovery, GPU benefit, upload, RSS, and resource budgets

- should meet warm latency, recovery, GPU benefit, upload, RSS, and resource budgets
- Measure warm font rendering and resource bounds
- fail test


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should meet warm latency, recovery, GPU benefit, upload, RSS, and resource budgets")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4f38ae8c328f37fff3270dca652ab501c408a4b93ad3a5906ec2a6243dd14e23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f38ae8c328f37fff3270dca652ab501c408a4b93ad3a5906ec2a6243dd14e23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f38ae8c328f37fff3270dca652ab501c408a4b93ad3a5906ec2a6243dd14e23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:516:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing or noncanonical SimpleOS artifact provenance' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:516:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing or noncanonical SimpleOS artifact provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:525:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed or ambiguous SimpleOS artifact hashes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:525:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject malformed or ambiguous SimpleOS artifact hashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:539:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject copied env-only SimpleOS artifact evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:539:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject copied env-only SimpleOS artifact evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:547:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify controlled missing native graphics hardware as unavailable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:558:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject forged pass labels without native device proof' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl:588:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should promote Engine2D and Engine3D fonts with a consistent Vulkan device tuple' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
