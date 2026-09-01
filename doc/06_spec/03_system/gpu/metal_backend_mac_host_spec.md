# Metal Backend Mac Host Specification

> Tests covering macOS Metal backend host verification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Backend Mac Host Specification

## Scenarios

### macOS Metal backend host verification

#### requires an explicit macOS Metal host capability

- requires an explicit macOS Metal host capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires an explicit macOS Metal host capability")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
pending("macOS host capability unavailable; live Metal evidence is postponed")
```

</details>

#### requires canonical Metal source-emission markers

- requires canonical Metal source-emission markers
   - Expected: file_exists(EMITTER) is true
   - Expected: file_exists(MSL) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires canonical Metal source-emission markers")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(file_exists(EMITTER)).to_equal(true)
expect(file_exists(MSL)).to_equal(true)
val emitter = file_read(EMITTER)
val msl = file_read(MSL)
expect(emitter).to_contain("PortableComputeTarget.Metal")
expect(emitter).to_contain("emit_portable_2d_optimization_module")
expect(emitter).to_contain("metal-shading-language")
expect(emitter).to_contain("kernel void {name}(")
expect(msl).to_contain("#include <metal_stdlib>")
expect(msl).to_contain("using namespace metal;")
expect(msl).to_contain("kernel void kernel_clear(")
expect(msl).to_contain("kernel void kernel_draw_rect_filled(")
expect(msl).to_contain("kernel void kernel_blit_image(")
expect(msl).to_contain("kernel void kernel_indexed_fill(")
expect(msl).to_contain("kernel void kernel_glyph_atlas_blit(")
```

</details>

#### keeps the admitted windowless MSL micro diagnostic bounded to library creation

- keeps the admitted windowless MSL micro diagnostic bounded to library creation
   - Expected: file_exists(MSL_MICRO_DIAGNOSTIC) is true
   - Expected: file_exists(MSL_MICRO_CHECK) is true
   - Expected: diagnostic does not contain `metal_sffi_create_command_queue`
   - Expected: diagnostic does not contain `metal_sffi_create_compute_pipeline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the admitted windowless MSL micro diagnostic bounded to library creation")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(file_exists(MSL_MICRO_DIAGNOSTIC)).to_equal(true)
expect(file_exists(MSL_MICRO_CHECK)).to_equal(true)
val diagnostic = file_read(MSL_MICRO_DIAGNOSTIC)
val checker = file_read(MSL_MICRO_CHECK)
expect(diagnostic).to_contain("macos-metal-msl-library-micro-v1")
expect(diagnostic).to_contain("metal_sffi_compile_shader(device, source)")
expect(diagnostic).to_contain("metal_msl_library_probe_device_create_status=")
expect(diagnostic.contains("metal_sffi_create_command_queue")).to_equal(false)
expect(diagnostic.contains("metal_sffi_create_compute_pipeline")).to_equal(false)
expect(checker).to_contain("verify_trusted_manifest")
expect(checker).to_contain("run_bounded_process")
```

</details>

#### requires the canonical native compile and readback receipt

- requires the canonical native compile and readback receipt
   - Expected: code equals `0`
   - Expected: file_exists(RECEIPT) is true
   - Expected: receipt_has(receipt, "metal_generated_2d_readback_status", "pass") is true
   - Expected: receipt_has(receipt, "metal_generated_2d_readback_module_verified", "true") is true
   - Expected: receipt_has(receipt, "metal_generated_2d_readback_submit_attempted", "true") is true
   - Expected: receipt_has(receipt, "metal_generated_2d_readback_readback_available", "true") is true
   - Expected: receipt_has(receipt, "metal_generated_2d_readback_provenance_status", "trusted-build-admitted-toolchain-verified") is true
   - Expected: receipt_has(receipt, "metal_generated_2d_readback_harness_exit_code", "0") is true
   - Expected: receipt_has(receipt, "metal_generated_2d_readback_reason", "gpu-readback-verified") is true
   - Expected: receipt_has(receipt, "metal_generated_2d_readback_mismatch_count", "0") is true
   - Expected: fill_checksum equals `fill_expected`
   - Expected: copy_checksum equals `copy_expected`
   - Expected: alpha_checksum equals `alpha_expected`
   - Expected: scroll_checksum equals `scroll_expected`
   - Expected: generated_checker does not contain `>"$harness_out" 2>"$harness_err" || true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires the canonical native compile and readback receipt")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
if not canonical_helpers_exist():
    fail_test("canonical Metal compile/readback helpers are missing")
    return
val (_stdout, _stderr, code) = run_native_receipt()
expect(code).to_equal(0)  # oracle: code must equal 0 — authoritative contract constant
expect(file_exists(RECEIPT)).to_equal(true)
val receipt = file_read(RECEIPT)
expect(receipt_has(receipt, "metal_generated_2d_readback_status", "pass")).to_equal(true)
expect(receipt_has(receipt, "metal_generated_2d_readback_module_verified", "true")).to_equal(true)
expect(receipt_has(receipt, "metal_generated_2d_readback_submit_attempted", "true")).to_equal(true)
expect(receipt_has(receipt, "metal_generated_2d_readback_readback_available", "true")).to_equal(true)
expect(receipt_has(receipt, "metal_generated_2d_readback_provenance_status", "trusted-build-admitted-toolchain-verified")).to_equal(true)
expect(receipt).to_contain("metal_generated_2d_readback_trusted_manifest=")
expect(receipt).to_contain("metal_generated_2d_readback_trusted_manifest_sha256=")
expect(receipt).to_contain("metal_generated_2d_readback_toolchain_manifest=")
expect(receipt).to_contain("metal_generated_2d_readback_toolchain_manifest_sha256=")
expect(receipt).to_contain("metal_generated_2d_readback_simple_bin_sha256=")
expect(receipt).to_contain("metal_generated_2d_readback_generated_source=")
expect(receipt).to_contain("metal_generated_2d_readback_generated_source_sha256=")
expect(receipt).to_contain("metal_generated_2d_readback_metallib_sha256=")
expect(receipt_has(receipt, "metal_generated_2d_readback_harness_exit_code", "0")).to_equal(true)
expect(receipt_has(receipt, "metal_generated_2d_readback_reason", "gpu-readback-verified")).to_equal(true)
expect(receipt_has(receipt, "metal_generated_2d_readback_mismatch_count", "0")).to_equal(true)
val fill_checksum = receipt_value(receipt, "metal_generated_2d_readback_fill_checksum")
val fill_expected = receipt_value(receipt, "metal_generated_2d_readback_fill_expected")
val copy_checksum = receipt_value(receipt, "metal_generated_2d_readback_copy_checksum")
val copy_expected = receipt_value(receipt, "metal_generated_2d_readback_copy_expected")
val alpha_checksum = receipt_value(receipt, "metal_generated_2d_readback_alpha_checksum")
val alpha_expected = receipt_value(receipt, "metal_generated_2d_readback_alpha_expected")
val scroll_checksum = receipt_value(receipt, "metal_generated_2d_readback_scroll_checksum")
val scroll_expected = receipt_value(receipt, "metal_generated_2d_readback_scroll_expected")
expect(fill_checksum.to_i64()).to_be_greater_than(0)
expect(copy_checksum.to_i64()).to_be_greater_than(0)
expect(alpha_checksum.to_i64()).to_be_greater_than(0)
expect(scroll_checksum.to_i64()).to_be_greater_than(0)
expect(fill_checksum).to_equal(fill_expected)
expect(copy_checksum).to_equal(copy_expected)
expect(alpha_checksum).to_equal(alpha_expected)
expect(scroll_checksum).to_equal(scroll_expected)
val generated_checker = file_read(GENERATED_CHECK)
expect(generated_checker).to_contain("macos_gpu_trusted_manifest_admit")
expect(generated_checker).to_contain("MACOS_GPU_ADMISSION_COMPILER")
expect(generated_checker).to_contain("REQUESTED_METALLIB_PATH")
expect(generated_checker).to_contain("metal_generated_source_sha256")
expect(generated_checker).to_contain("metal_artifact_sha256")
expect(generated_checker).to_contain("metal_generated_2d_readback_simple_bin_sha256")
expect(generated_checker).to_contain("harness_exit=$?")
expect(generated_checker).to_contain("harness-exit-status-")
expect(generated_checker.contains(">\"$harness_out\" 2>\"$harness_err\" || true")).to_equal(false)
expect(generated_checker).to_contain("readback_positive_decimal")
expect(generated_checker).to_contain("gpu-readback-verified")
```

</details>

#### renders exact pixels through production Metal without a CPU mirror

- renders exact pixels through production Metal without a CPU mirror
   - Expected: backend.init(16, 16) is true
   - Expected: backend.gpu_frame_complete is true
   - Expected: clear_readback.source equals `device_readback`
   - Expected: clear_readback.pixels.len() equals `16 * 16`
   - Expected: clear_readback.pixels[clear_i] equals `black`
   - Expected: backend.gpu_frame_complete is true
   - Expected: rect_readback.source equals `device_readback`
   - Expected: rect_readback.backend_handle equals `clear_readback.backend_handle`
   - Expected: rect_readback.device_identity equals `clear_readback.device_identity`
   - Expected: rect_readback.pixels.len() equals `16 * 16`
   - Expected: rect_readback.pixels[y * 16 + x] equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders exact pixels through production Metal without a CPU mirror")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
var backend = MetalBackend.create()
expect(backend.init(16, 16)).to_equal(true)
backend.use_gpu_only()

val black = rgb(0, 0, 0)
val red = rgb(255, 0, 0)
backend.clear(black)
expect(backend.gpu_frame_complete).to_equal(true)
val clear_readback = backend.read_pixels_with_source()
expect(clear_readback.source).to_equal("device_readback")
expect(clear_readback.backend_handle).to_be_greater_than(0)
expect(clear_readback.device_identity).to_be_greater_than(0)
expect(clear_readback.pixels.len()).to_equal(16 * 16)
var clear_i: i32 = 0
while clear_i < 16 * 16:
    expect(clear_readback.pixels[clear_i]).to_equal(black)
    clear_i = clear_i + 1

backend.draw_rect_filled(4, 4, 8, 8, red)
expect(backend.gpu_frame_complete).to_equal(true)
val rect_readback = backend.read_pixels_with_source()
expect(rect_readback.source).to_equal("device_readback")
expect(rect_readback.backend_handle).to_equal(clear_readback.backend_handle)
expect(rect_readback.device_identity).to_equal(clear_readback.device_identity)
expect(rect_readback.pixels.len()).to_equal(16 * 16)
var y: i32 = 0
while y < 16:
    var x: i32 = 0
    while x < 16:
        val expected = if x >= 4 and x < 12 and y >= 4 and y < 12: red else: black
        expect(rect_readback.pixels[y * 16 + x]).to_equal(expected)
        x = x + 1
    y = y + 1
backend.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/03_system/gpu/metal_backend_mac_host_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering macOS Metal backend host verification.
- macOS Metal backend host verification

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `29566c6d369716da5d2e627298eb79cc106e3f63b720e3cbba7fdde13bf53c7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29566c6d369716da5d2e627298eb79cc106e3f63b720e3cbba7fdde13bf53c7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29566c6d369716da5d2e627298eb79cc106e3f63b720e3cbba7fdde13bf53c7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gpu/metal_backend_mac_host_spec.spl
mirror: doc/06_spec/03_system/gpu/metal_backend_mac_host_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/gpu/metal_backend_mac_host_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gpu/metal_backend_mac_host_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gpu/metal_backend_mac_host_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->
