# Backend Metal Mac Host Resume Contract Specification

> Tests covering Metal macOS host resume contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Metal Mac Host Resume Contract Specification

## Scenarios

### Metal macOS host resume contract

#### keeps every prepared-host script and test path present and listed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every prepared-host script and test path present and listed
   - Expected: file_exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps every prepared-host script and test path present and listed")
val plan = file_read("doc/03_plan/agent_tasks/gpu_backend_mac_host_remaining.md")
val paths = [
    "scripts/check/check-portable-compute-toolchains.shs",
    "scripts/check/check-metal-generated-2d-readback.shs",
    "scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs",
    "scripts/check/check-engine2d-cpu-metal-parity-evidence.shs",
    "scripts/check/check-macos-metal-msl-library-micro-diagnostic.shs",
    "scripts/check/check-macos-gpu-2d-live-evidence.shs",
    "test/02_integration/rendering/macos_metal_msl_library_micro_diagnostic.spl",
    "test/03_system/gpu/metal_backend_mac_host_spec.spl",
    "test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl",
    "test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl",
    "test/05_perf/web_render_chrome/web_gpu_paint_device_measured_spec.spl",
    "test/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.spl"
]
for path in paths:
    expect(file_exists(path)).to_equal(true)
    expect(plan).to_contain(path)
```

</details>

#### keeps the prepared-host commands, evidence gate, and producer path

- keeps the prepared-host commands, evidence gate, and producer path
   - Expected: host_spec).to_contain("expect(backend.gpu_frame_complete is true
   - Expected: host_spec).to_contain("expect(rect_readback.source equals `"device_readback")"`
   - Expected: host_spec).to_contain("expect(rect_readback.backend_handle equals `clear_readback.backend_handle)"`
   - Expected: host_spec).to_contain("expect(rect_readback.device_identity equals `clear_readback.device_identity)"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the prepared-host commands, evidence gate, and producer path")
val plan = file_read("doc/03_plan/agent_tasks/gpu_backend_mac_host_remaining.md")
expect(plan).to_contain("test/03_system/gpu/metal_backend_mac_host_spec.spl")
expect(plan).to_contain("GPU_2D_LIVE_BACKEND=metal")
expect(plan).to_contain("sh scripts/check/check-macos-gpu-2d-live-evidence.shs")
expect(plan).to_contain("metal_generated_2d_readback_status=pass")
expect(plan).to_contain("Linux or unavailable output is not a pass.")

val host_spec = file_read("test/03_system/gpu/metal_backend_mac_host_spec.spl")
expect(host_spec).to_contain("backend.use_gpu_only()")
expect(host_spec).to_contain("expect(backend.gpu_frame_complete).to_equal(true)")
expect(host_spec).to_contain("expect(rect_readback.source).to_equal(\"device_readback\")")
expect(host_spec).to_contain("expect(rect_readback.backend_handle).to_equal(clear_readback.backend_handle)")
expect(host_spec).to_contain("expect(rect_readback.device_identity).to_equal(clear_readback.device_identity)")

val gate = file_read("scripts/check/check-macos-gpu-2d-live-evidence.shs")
val root_var = "$" + "ROOT_DIR"
val backend_var = "$" + "{" + "BACKEND" + "}"
expect(gate).to_contain("HARNESS=\"" + root_var + "/test/02_integration/rendering/macos_" + backend_var + "_2d_live_harness.spl\"")
expect(gate).to_contain("BACKEND_SOURCE=\"" + root_var + "/src/lib/gc_async_mut/gpu/engine2d/backend_" + backend_var + ".spl\"")
expect(gate).to_contain("gpu_2d_live_source")
expect(gate).to_contain("device_readback")
expect(gate).to_contain("gpu_2d_live_draw_ir_fallback_required")

val producer = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl")
expect(producer).to_contain("me use_gpu_only():")
expect(producer).to_contain("metal_sffi_dispatch_compute")
expect(producer).to_contain("metal_sffi_commit_command_buffer")
expect(producer).to_contain("metal_sffi_wait_completed")
expect(producer).to_contain("readback_source_label(ReadbackSource.DeviceReadback)")
```

</details>

#### keeps GPU-only image blending on native Metal before explicit fallback

- keeps GPU-only image blending on native Metal before explicit fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps GPU-only image blending on native Metal before explicit fallback")
val producer = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl")
expect(producer).to_contain(
    "val native_completed = self.draw_image_blend_checked(")
expect(producer).to_contain(
    "not self._gpu_only_mask_emulation_active()")
expect(producer).to_contain("x, y, w, h, pixels, 1000)")
expect(producer).to_contain(
    "if not self.initialized:")
expect(producer).to_contain(
    "self.gpu_frame_complete = was_complete")
expect(producer).to_contain(
    "self.last_image_blend_target = \"metal\"")
expect(producer).to_contain(
    "return engine2d_readback([], \"completion_unknown\")")
expect(producer).to_contain(
    "return engine2d_readback([], \"readback_failed\")")
expect(producer).to_contain("self.mirror.draw_image_blend(x, y, w, h, pixels)")

val readback_spec = file_read(
    "test/02_integration/rendering/metal_engine2d_readback_spec.spl")
expect(readback_spec).to_contain("if is_macos():")
expect(readback_spec).to_contain(
    "expect(is_macos()).to_equal(false)")
expect(readback_spec).to_contain(
    "b.draw_image_blend(0, 0, 1, 1, [0x80ffffffu32])")
expect(readback_spec).to_contain(
    "expect(b.last_image_blend_target).to_equal(\"metal\")")
expect(readback_spec).to_contain(
    "expect(receipt.source).to_equal(\"device_readback\")")
expect(readback_spec).to_contain(
    "expect(receipt.pixels[0]).to_equal(0xff808080u32)")
```

</details>

#### pins generated Metal submission, download, and exact checksum gates

- pins generated Metal submission, download, and exact checksum gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins generated Metal submission, download, and exact checksum gates")
val generated = file_read(
    "scripts/check/metal_generated_2d_readback_harness.spl")
val gate = file_read(
    "scripts/check/check-metal-generated-2d-readback.shs")
val micro_gate = file_read(
    "scripts/check/check-macos-metal-msl-library-micro-diagnostic.shs")
expect(generated).to_contain("rt_metal_create_device(0)")
expect(generated).to_contain("rt_metal_create_compute_pipeline")
expect(generated).to_contain("rt_metal_dispatch_compute")
expect(generated).to_contain("rt_metal_commit_command_buffer")
expect(generated).to_contain("rt_metal_wait_completed")
expect(generated).to_contain("rt_metal_buffer_download")
expect(generated).to_contain("print(\"submit_attempted=")
expect(generated).to_contain("print(\"readback_available=")
expect(gate).to_contain(
    "MTLDevice -> host upload -> compute pipeline -> submit -> wait -> host download")
expect(gate).to_contain(
    "metal_generated_2d_readback_module_verified=$module_verified")
expect(gate).to_contain(
    "metal_generated_2d_readback_submit_attempted=$h_submit")
expect(gate).to_contain(
    "metal_generated_2d_readback_readback_available=$h_readback")
expect(gate).to_contain(
    "metal_generated_2d_readback_expected_checksum=$h_expected")
expect(gate).to_contain(
    "metal_generated_2d_readback_actual_checksum=$h_actual")
expect(gate).to_contain(
    "metal_generated_2d_readback_mismatch_count=$h_mismatch_count")
expect(gate).to_contain("macos_gpu_trusted_manifest_admit")
expect(gate).to_contain("MACOS_GPU_ADMISSION_COMPILER")
expect(gate).to_contain("REQUESTED_METALLIB_PATH")
expect(gate).to_contain("metal_generated_source_sha256")
expect(gate).to_contain("metal_artifact_sha256")
expect(gate).to_contain(
    "PROVENANCE_STATUS=\"trusted-build-admitted-toolchain-verified\"")
expect(gate).to_contain(
    "metal_generated_2d_readback_harness_exit_code=$harness_exit")
expect(gate).to_contain("reason=\"harness-exit-status-$harness_exit\"")
expect(gate).to_contain("harness_exit=$?")
expect(gate).to_contain("command -v sha256sum")
expect(gate).to_contain("command -v shasum")
expect(micro_gate).to_contain("macos_gpu_trusted_manifest_admit")
expect(micro_gate).to_contain("command -v sha256sum")
expect(micro_gate).to_contain("command -v shasum")
expect(gate.contains(
    ">\"$harness_out\" 2>\"$harness_err\" || true")).to_equal(false)
for op in ["fill", "copy", "alpha", "scroll"]:
    expect(gate).to_contain("metal_generated_2d_readback_{op}_checksum=")
    expect(gate).to_contain("metal_generated_2d_readback_{op}_expected=")
expect(gate).to_contain("reason=\"gpu-readback-verified\"")
expect(gate).to_contain(
    "elif [ \"$h_actual\" != \"$h_expected\" ]; then")
```

</details>

#### pins device-origin framebuffer, parity, and no-fallback gates

- pins device-origin framebuffer, parity, and no-fallback gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins device-origin framebuffer, parity, and no-fallback gates")
val framebuffer = file_read(
    "scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs")
val parity_gate = file_read(
    "scripts/check/check-engine2d-cpu-metal-parity-evidence.shs")
val parity_harness = file_read(
    "test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl")
val live = file_read("scripts/check/check-macos-gpu-2d-live-evidence.shs")
val processing = file_read(
    "test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl")
expect(framebuffer).to_contain(
    "metal_buffer_download_ptr(host, self.d_framebuffer")
expect(framebuffer).to_contain("gpu_frame_complete")
expect(framebuffer).to_contain("raw-metal-framebuffer-download-proven")
expect(framebuffer).to_contain(
    "metal_engine2d_framebuffer_exact_gpu_claimed=$read_pixels_gpu_download")
expect(framebuffer).to_contain(
    "metal_engine2d_framebuffer_blur_or_tolerance_used=false")
expect(parity_harness).to_contain("gpu_frame_complete")
expect(parity_harness).to_contain(
    "metal-fell-back-to-cpu-mirror gpu_ok=false")
expect(parity_harness).to_contain("MATCH mismatches=0/")
expect(parity_harness).to_contain("gpu_ok=true")
expect(parity_harness).to_contain("PARITY: pass")
expect(parity_gate).to_contain("REASON=cpu-metal-bitexact")
expect(parity_gate).to_contain("REASON=pixel-divergence")
expect(parity_gate).to_contain(
    "engine2d_cpu_metal_parity_policy=exact-bitmap-no-blur-no-tolerance")
expect(live).to_contain("device_readback")
expect(live).to_contain("gpu_2d_live_draw_ir_fallback_required")
expect(live).to_contain("processing_ir_cpu_fallback")
expect(live).to_contain("processing-ir-receipt-cpu-fallback")
expect(live).to_contain("positive_integer \"$processing_ir_handle\"")
expect(live).to_contain("positive_integer \"$processing_ir_identity\"")
expect(live).to_contain("capture-header-mismatch")
expect(live).to_contain("pixel-sha256-invalid")
expect(live).to_contain("command -v sha256sum")
expect(live).to_contain("command -v shasum")
expect(processing).to_contain("require_processing_ir_receipt(receipt)")
expect(processing).to_contain("PROCESSING_IR_EXPECTED_CHECKSUM")
expect(processing).to_contain("PROCESSING_IR_ACTUAL_CHECKSUM")
expect(processing).to_contain("PROCESSING_IR_VALUES_EXACT")
expect(processing).to_contain("PROCESSING_IR_MISMATCH_COUNT")
expect(processing).to_contain("PROCESSING_IR_CPU_FALLBACK")
```

</details>

#### pins the prepared 21-pair revision-cache speed and provenance gate

- pins the prepared 21-pair revision-cache speed and provenance gate
   - Expected: cache).to_contain("expect(mismatches equals `0)"`
   - Expected: cache).to_contain("expect(provenance_mismatches equals `0)"`
   - Expected: cache).to_contain("expect(readback_source equals `"device_readback")"`
   - Expected: cache).to_contain("expect(raster.revision_reuse_count equals `"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins the prepared 21-pair revision-cache speed and provenance gate")
val cache_plan = file_read(
    "doc/03_plan/agent_tasks/gpu_backend_mac_host_remaining.md")
val cache = file_read(
    "test/05_perf/browser/hosted_compositor_revision_cache_perf_spec.spl")
expect(cache_plan).to_contain("SIMPLE_HOSTED_REVISION_CACHE_BACKEND=metal")
expect(cache_plan).to_contain("SIMPLE_HOSTED_REVISION_CACHE_BACKEND=vulkan")
expect(cache_plan).to_contain(
    "hosted compositor revision-cache benchmark records 21 paired forced and")
expect(cache_plan).to_contain(
    "unchanged frames for both Metal and Vulkan.")
expect(cache_plan).to_contain("hit_p50_ns * 100 < forced_p50_ns * 95")
expect(cache_plan).to_contain("not a CPU mirror or fallback")
expect(cache).to_contain("val TIMED_PAIRS: i64 = 21")
expect(cache).to_contain("if (forced.pixels != expected_pixels or")
expect(cache).to_contain("provenance_mismatches")
expect(cache).to_contain("expect(mismatches).to_equal(0)")
expect(cache).to_contain("expect(provenance_mismatches).to_equal(0)")
expect(cache).to_contain(
    "expect(hit_p50_ns * 100).to_be_less_than(forced_p50_ns * 95)")
expect(cache).to_contain("expect(readback_source).to_equal(\"device_readback\")")
expect(cache).to_contain("expect(backend_handle).to_be_greater_than(0)")
expect(cache).to_contain("expect(device_identity).to_be_greater_than(0)")
expect(cache).to_contain("expect(raster.revision_reuse_count).to_equal(")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_mac_host_resume_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Metal macOS host resume contract.
- Metal macOS host resume contract

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

- Canonical SPipe generation for source `211ce004955707d484f0f153fed4a4534b09eaad32959ce60e4040d460396e38`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `211ce004955707d484f0f153fed4a4534b09eaad32959ce60e4040d460396e38`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `211ce004955707d484f0f153fed4a4534b09eaad32959ce60e4040d460396e38`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_mac_host_resume_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_mac_host_resume_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_mac_host_resume_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_mac_host_resume_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_mac_host_resume_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every prepared-host script and test path present and listed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_mac_host_resume_contract_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the prepared-host commands, evidence gate, and producer path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_mac_host_resume_contract_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps GPU-only image blending on native Metal before explicit fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
