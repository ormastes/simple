# Engine2D Font Surface Verification

> Drives the public Engine2D requested-backend facade with the pinned Noto Sans

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Font Surface Verification

Drives the public Engine2D requested-backend facade with the pinned Noto Sans

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Drives the public Engine2D requested-backend facade with the pinned Noto Sans
Mono asset. The CPU lane is the exact packed-ARGB oracle. On x86_64, the
`cpu_simd` request must preserve every absolute framebuffer
pixel while proving native glyph-alpha rows; Vulkan must disclose real device
submission and readback or fail as unavailable.

## Scenarios

### Engine2D pinned-font rendering surfaces

#### keeps the cpu_simd request pixel-exact with native glyph alpha rows

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Primary flow (expected show, folded, detail, or skip)


- keeps the cpu_simd request pixel-exact with native glyph alpha rows
   - Artifact capture: after_step
- Load the pinned multilingual font manifest
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: file_hash_sha256(FONT_PATH) equals `FONT_SHA256`
   - Expected: TEXT equals `Simple 2D`
- Accept exact-face-bound simple-script shaping
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: cpu.backend equals `cpu`
   - Expected: cpu.source equals `cpu_mirror`
   - Expected: cpu.execution_target equals `cpu`
- Prepare one shared font batch for 2D and 3D
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: simd.backend equals `cpu_simd`
   - Expected: simd.source equals `cpu_mirror`
   - Expected: simd.execution_target equals `cpu_simd`
- Emit the selected font composite program and plan compilation
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: simd.pixels equals `cpu.pixels`
- Prove native submission and device readback
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: cpu.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: simd.painted equals `cpu.painted`
   - Expected: simd.partial equals `cpu.partial`
   - Expected: simd.min_x equals `cpu.min_x`
   - Expected: simd.min_y equals `cpu.min_y`
   - Expected: simd.max_x equals `cpu.max_x`
   - Expected: simd.max_y equals `cpu.max_y`
   - Expected: simd.simd_native_hits equals `simd.simd_alpha_hits`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the cpu_simd request pixel-exact with native glyph alpha rows")
"""The canonical CPU engine and cpu_simd request consume one semantic string and one selected face.

The comparison is exact over all 9,216 absolute packed-ARGB pixels; a
checksum, tolerance, or separately painted SIMD fixture is insufficient.
"""
expect(_is_interpreter_mode()).to_be(false)
step("Load the pinned multilingual font manifest")
expect(file_hash_sha256(FONT_PATH)).to_equal(FONT_SHA256)
expect(TEXT).to_equal("Simple 2D")

step("Accept exact-face-bound simple-script shaping")
val cpu = require_render("cpu")
expect(cpu.backend).to_equal("cpu")
expect(cpu.source).to_equal("cpu_mirror")
expect(cpu.execution_target).to_equal("cpu")
expect(cpu.attempts).to_contain("cpu:success")

step("Prepare one shared font batch for 2D and 3D")
val simd = require_render("cpu_simd")
expect(simd.backend).to_equal("cpu_simd")
expect(simd.source).to_equal("cpu_mirror")
expect(simd.execution_target).to_equal("cpu_simd")
expect(simd.attempts).to_contain("cpu_simd:success")

step("Emit the selected font composite program and plan compilation")
expect(simd.pixels).to_equal(cpu.pixels)

step("Prove native submission and device readback")
expect(cpu.pixels.len()).to_equal(WIDTH * HEIGHT)
expect(cpu.painted).to_be_greater_than(0)
expect(cpu.partial).to_be_greater_than(0)
expect(simd.painted).to_equal(cpu.painted)
expect(simd.partial).to_equal(cpu.partial)
expect(simd.min_x).to_equal(cpu.min_x)
expect(simd.min_y).to_equal(cpu.min_y)
expect(simd.max_x).to_equal(cpu.max_x)
expect(simd.max_y).to_equal(cpu.max_y)
expect(simd.simd_alpha_hits).to_be_greater_than(0)
expect(simd.simd_native_hits).to_be_greater_than(0)
expect(simd.simd_native_hits).to_equal(simd.simd_alpha_hits)
expect(cpu.min_x).to_be_greater_than(7)
expect(cpu.min_y).to_be_greater_than(7)
expect(cpu.max_x).to_be_less_than(WIDTH)
expect(cpu.max_y).to_be_less_than(HEIGHT)
retain_capture("cpu", cpu.pixels)
retain_capture("cpu_simd", simd.pixels)
```

</details>

#### renders the same absolute pixels only after Vulkan device readback

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Vulkan device row (expected show, folded, detail, or skip)


- renders the same absolute pixels only after Vulkan device readback
   - Artifact capture: after_step
- Load the pinned multilingual font manifest
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: file_hash_sha256(FONT_PATH) equals `FONT_SHA256`
   - Expected: TEXT equals `Simple 2D`
- Accept exact-face-bound simple-script shaping
   - Artifact capture: after_step
- Prepare one shared font batch for 2D and 3D
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: vulkan.backend equals `vulkan`
   - Expected: vulkan.execution_target equals `vulkan`
   - Expected: vulkan.attempts equals `vulkan:fence-device-identity-readback-proven`
- Emit the selected font composite program and plan compilation
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: vulkan.pixels equals `cpu.pixels`
- Prove native submission and device readback
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: vulkan.source equals `device_readback`
   - Expected: vulkan.painted equals `cpu.painted`
   - Expected: vulkan.partial equals `cpu.partial`
   - Expected: vulkan.min_x equals `cpu.min_x`
   - Expected: vulkan.min_y equals `cpu.min_y`
   - Expected: vulkan.max_x equals `cpu.max_x`
   - Expected: vulkan.max_y equals `cpu.max_y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders the same absolute pixels only after Vulkan device readback")
"""Vulkan cannot pass through software fallback, a CPU mirror, or backend-name relabeling.

A host without an accelerated, fenced Vulkan font compositor reports a
failing unavailable row so the capability remains visible.
"""
step("Load the pinned multilingual font manifest")
expect(file_hash_sha256(FONT_PATH)).to_equal(FONT_SHA256)
expect(TEXT).to_equal("Simple 2D")

step("Accept exact-face-bound simple-script shaping")
val cpu = require_render("cpu")

step("Prepare one shared font batch for 2D and 3D")
val vulkan = require_render("vulkan")
expect(vulkan.backend).to_equal("vulkan")
expect(vulkan.execution_target).to_equal("vulkan")
expect(vulkan.attempts).to_equal("vulkan:fence-device-identity-readback-proven")

step("Emit the selected font composite program and plan compilation")
expect(vulkan.pixels).to_equal(cpu.pixels)

step("Prove native submission and device readback")
expect(vulkan.source).to_equal("device_readback")
expect(vulkan.backend_handle).to_be_greater_than(0)
expect(vulkan.device_identity).to_be_greater_than(0)
expect(vulkan.painted).to_equal(cpu.painted)
expect(vulkan.partial).to_equal(cpu.partial)
expect(vulkan.min_x).to_equal(cpu.min_x)
expect(vulkan.min_y).to_equal(cpu.min_y)
expect(vulkan.max_x).to_equal(cpu.max_x)
expect(vulkan.max_y).to_equal(cpu.max_y)
retain_capture("vulkan", vulkan.pixels)
```

</details>

#### submits resolved DrawIR text through the canonical font consumer

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: DrawIR production boundary (expected show, folded, detail, or skip)


- submits resolved DrawIR text through the canonical font consumer
   - Artifact capture: after_step
- Trace the production font and event boundary
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: metrics.advances.len() equals `TEXT.len()`
   - Expected: command.text_value equals `TEXT`
   - Expected: command.computed_style.len() equals `5`
- Submit the boundary output to its canonical consumer
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: result.rendered_command_count equals `2`
   - Expected: result.skipped_command_count equals `0`
   - Expected: result.readback_source equals `cpu_mirror`
- Correlate visible pixels and input with one frame identity
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: result.pixels equals `direct.pixels`
   - Expected: result.pixels.len() equals `WIDTH * HEIGHT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("submits resolved DrawIR text through the canonical font consumer")
step("Trace the production font and event boundary")
val metrics = resolve_font_metrics(FONT_PATH, TEXT, 24)
expect(metrics.valid).to_be(true)
expect(metrics.identity).to_contain("NotoSansMono")
expect(metrics.advances.len()).to_equal(TEXT.len())
val command = draw_ir_text_resolved_font("font-surface-text", 8, 8, TEXT, FG,
    metrics.family, metrics.identity, metrics.advances, metrics.width, metrics.line_height, 24)
expect(command.text_value).to_equal(TEXT)
expect(command.computed_style.len()).to_equal(5)

step("Submit the boundary output to its canonical consumer")
val embedding = draw_ir_embedding_config("", "font-surface", 0, 0, WIDTH, HEIGHT, 0, 1000, true)
val composition = draw_ir_composition("font-surface-frame", "engine2d-font-surface", "cpu", [
    draw_ir_batch("font-surface-batch", "cpu", embedding, [
        draw_ir_rect("font-surface-background", 0, 0, WIDTH, HEIGHT, BG), command
    ])
])
var engine = Engine2D.create_with_backend(WIDTH, HEIGHT, "cpu")
expect(engine.load_font(FONT_PATH)).to_be(true)
val result = engine2d_draw_ir_adv_composition(engine, composition, false)
expect(result.rendered_command_count).to_equal(2)
expect(result.skipped_command_count).to_equal(0)
expect(result.readback_source).to_equal("cpu_mirror")

step("Correlate visible pixels and input with one frame identity")
val direct = require_render("cpu")
expect(result.pixels).to_equal(direct.pixels)
expect(result.pixels.len()).to_equal(WIDTH * HEIGHT)
retain_capture("draw_ir_cpu", result.pixels)
engine.shutdown()
```

</details>

<details>
<summary>Advanced: rejects inconsistent DrawIR font advances before rendering</summary>

#### rejects inconsistent DrawIR font advances before rendering

- rejects inconsistent DrawIR font advances before rendering
- Trace the production font and event boundary
- Submit the boundary output to its canonical consumer
- Reject disconnected stale or replayed evidence
   - Expected: result.readback_source equals `preflight_rejected`
   - Expected: result.rendered_command_count equals `0`
   - Expected: result.skipped_command_count equals `1`
   - Expected: result.pixels.len() equals `0`
   - Expected: engine.read_pixels() equals `[BG; WIDTH * HEIGHT]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects inconsistent DrawIR font advances before rendering")
step("Trace the production font and event boundary")
val metrics = resolve_font_metrics(FONT_PATH, TEXT, 24)
expect(metrics.valid).to_be(true)
var replayed = draw_ir_text_resolved_font("font-surface-replay", 8, 8, TEXT, FG,
    metrics.family, metrics.identity, metrics.advances, metrics.width, metrics.line_height, 24)
replayed.computed_style[2].value = "1"

step("Submit the boundary output to its canonical consumer")
val embedding = draw_ir_embedding_config("", "font-surface", 0, 0, WIDTH, HEIGHT, 0, 1000, true)
val composition = draw_ir_composition("font-surface-replayed-frame", "engine2d-font-surface", "cpu", [
    draw_ir_batch("font-surface-replayed-batch", "cpu", embedding, [
        draw_ir_rect("font-surface-background", 0, 0, WIDTH, HEIGHT, BG), replayed
    ])
])
var engine = Engine2D.create_with_backend(WIDTH, HEIGHT, "cpu")
engine.clear(BG)

step("Reject disconnected stale or replayed evidence")
val result = engine2d_draw_ir_adv_fresh_device_composition_with_images(engine, composition, [])
expect(result.readback_source).to_equal("preflight_rejected")
expect(result.rendered_command_count).to_equal(0)
expect(result.skipped_command_count).to_equal(1)
expect(result.pixels.len()).to_equal(0)
expect(engine.read_pixels()).to_equal([BG; WIDTH * HEIGHT])
engine.shutdown()
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `88efc070e5f1bd1c3b862b8b72c1139170b4b532cca7fde6ffa80b54619799b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88efc070e5f1bd1c3b862b8b72c1139170b4b532cca7fde6ffa80b54619799b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88efc070e5f1bd1c3b862b8b72c1139170b4b532cca7fde6ffa80b54619799b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the cpu_simd request pixel-exact with native glyph alpha rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl:186:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders the same absolute pixels only after Vulkan device readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/engine2d_font_surface_verification_spec.spl:225:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'submits resolved DrawIR text through the canonical font consumer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
