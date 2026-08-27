# Macos Vulkan Processing Ir Live Readback Parity Specification

> Tests covering macOS Vulkan ProcessingIR 2D live readback parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macos Vulkan Processing Ir Live Readback Parity Specification

## Scenarios

### macOS Vulkan ProcessingIR 2D live readback parity

#### runs the canonical Vulkan checker and admits only real device evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the canonical Vulkan checker and admits only real device evidence
   - Expected: file_exists(FRONTEND) is true
   - Expected: code equals `0`
   - Expected: file_exists(RECEIPT) is true
   - Expected: file_exists(EVIDENCE) is true
   - Expected: receipt contains `gpu_2d_live_draw_ir_fallback_reason=\n`
   - Expected: nonempty_field(receipt, "gpu_2d_live_backend_handle") is true
   - Expected: receipt does not contain `gpu_2d_live_backend_handle=0\n`
   - Expected: nonempty_field(receipt, "gpu_2d_live_initial_checksum") is true
   - Expected: nonempty_field(receipt, "gpu_2d_live_interaction_checksum") is true
   - Expected: nonempty_field(receipt, "gpu_2d_live_draw_ir_readback_checksum") is true
   - Expected: nonempty_field(evidence, "macos_vulkan_2d_live_pixel_sha256") is true
   - Expected: receipt_value(receipt, "gpu_2d_live_fallback") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the canonical Vulkan checker and admits only real device evidence")
if not is_macos():
    pending("macOS host capability unavailable; live Vulkan evidence is postponed")
    return
expect(file_exists(FRONTEND)).to_equal(true)
val (_stdout, _stderr, code) = process_run("/bin/sh", [FRONTEND])
expect(code).to_equal(0)
expect(file_exists(RECEIPT)).to_equal(true)
expect(file_exists(EVIDENCE)).to_equal(true)

val receipt = file_read(RECEIPT)
val evidence = file_read(EVIDENCE)
expect(receipt).to_contain("gpu_2d_live_status=pass")
expect(receipt).to_contain("gpu_2d_live_backend=vulkan")
expect(receipt).to_contain("gpu_2d_live_source=device_readback")
expect(receipt).to_contain("gpu_2d_live_draw_ir_readback_source=device_readback")
expect(receipt).to_contain("gpu_2d_live_draw_ir_fallback_required=false")
expect(receipt).to_contain("gpu_2d_live_draw_ir_skipped_commands=0")
expect(receipt.contains("gpu_2d_live_draw_ir_fallback_reason=\n")).to_equal(true)

# The current canonical schema proves a positive native handle and
# hashes the complete device capture.
expect(nonempty_field(receipt, "gpu_2d_live_backend_handle")).to_equal(true)
expect(receipt.contains("gpu_2d_live_backend_handle=0\n")).to_equal(false)
expect(receipt).to_contain("gpu_2d_live_width=3840")
expect(receipt).to_contain("gpu_2d_live_height=2160")
expect(nonempty_field(receipt, "gpu_2d_live_initial_checksum")).to_equal(true)
expect(nonempty_field(receipt, "gpu_2d_live_interaction_checksum")).to_equal(true)
expect(nonempty_field(receipt, "gpu_2d_live_draw_ir_readback_checksum")).to_equal(true)
expect(nonempty_field(evidence, "macos_vulkan_2d_live_pixel_sha256")).to_equal(true)

expect(receipt_value(receipt, "gpu_2d_live_fallback")).to_equal("false")

require_processing_ir_receipt(receipt)
```

</details>

#### keeps device-only admission in the canonical checker

- keeps device-only admission in the canonical checker
   - Expected: checker does not contain `cpu_mirror`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps device-only admission in the canonical checker")
val frontend = file_read(FRONTEND)
val checker = file_read(CHECKER)
expect(frontend).to_contain("GPU_2D_LIVE_BACKEND=vulkan")
expect(checker).to_contain("device-readback-missing")
expect(checker).to_contain("backend-handle-missing")
expect(checker).to_contain("capture-header-mismatch")
expect(checker).to_contain("pixel-sha256-invalid")
expect(checker).to_contain("shared-draw-ir-fallback-required")
expect(checker).to_contain("device_readback")
expect(checker.contains("cpu_mirror")).to_equal(false)
```

</details>

#### keeps ProcessingIR receipt fields owned by the macOS harness

- keeps ProcessingIR receipt fields owned by the macOS harness


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps ProcessingIR receipt fields owned by the macOS harness")
val harness = file_read(HARNESS)
val checker = file_read(CHECKER)
for field in [
    "processing_ir_status", "processing_ir_backend", "processing_ir_count",
    "processing_ir_expected_checksum", "processing_ir_actual_checksum",
    "processing_ir_values_exact", "processing_ir_readback_source",
    "processing_ir_handle", "processing_ir_identity",
    "processing_ir_mismatch_count", "processing_ir_cpu_fallback"
]:
    expect(harness).to_contain("gpu_2d_live_{field}=")
    expect(checker).to_contain("gpu_2d_live_{field}")
expect(harness).to_contain("device_readback")
expect(harness).to_contain("expected_checksum")
expect(harness).to_contain("actual_checksum")
expect(harness).to_contain(
    "gpu_2d_live_processing_ir_reason={result.reason}")
expect(harness).to_contain(
    "gpu_2d_live_processing_ir_completed={result.completed}")
expect(harness).to_contain("write_failure_receipt_with_diagnostics")
expect(harness).to_contain(
    "receipt_path, backend, \"processing-ir-receipt-failed\", 4, 4,")
expect(harness).to_contain("receipt_lines)")
expect(harness).to_contain(
    "\"gpu_2d_live_exit_code={exit_code}\\n\" +")
expect(harness).to_contain("        diagnostics)\n    exit_code")
expect(checker).to_contain("processing-ir-receipt")
```

</details>

#### uses the scoped byte-array SPIR-V ABI outside the interpreter

- uses the scoped byte-array SPIR-V ABI outside the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses the scoped byte-array SPIR-V ABI outside the interpreter")
val source = file_read(VULKAN_IO_SFFI)
expect(source).to_contain("gpu_sffi_uses_interpreter_array_abi")
expect(source).to_contain(
    "extern fn rt_vulkan_compile_spirv_array(bytes: [u8])")
expect(source).to_contain("fn _vulkan_compile_spirv_abi")
expect(source).to_contain(
    "return rt_vulkan_compile_spirv(spirv_bytes)")
expect(source).to_contain(
    "rt_vulkan_compile_spirv_array(spirv_bytes)")
expect(source).to_contain(
    "val handle = _vulkan_compile_spirv_abi(spirv_bytes)")
```

</details>

#### invalidates stale or caller-forged receipts before admission

- invalidates stale or caller-forged receipts before admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("invalidates stale or caller-forged receipts before admission")
val checker = file_read(CHECKER)
expect(checker).to_contain("rm -f \"$CAPTURE_PPM\"")
expect(checker).to_contain("repo-revision-mismatch")
expect(checker).to_contain("source-revision-mismatch")
expect(checker).to_contain("trusted-build-manifest-invalid")
expect(checker).to_contain("arbitrary-native-driver-supplied")
expect(checker).to_contain("runtime-receipt-timeout")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering macOS Vulkan ProcessingIR 2D live readback parity.
- macOS Vulkan ProcessingIR 2D live readback parity

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

- Canonical SPipe generation for source `53b676894220862bd668df6df54dc0435ae0df481938fe3f00a8dbe2c814f453`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `53b676894220862bd668df6df54dc0435ae0df481938fe3f00a8dbe2c814f453`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `53b676894220862bd668df6df54dc0435ae0df481938fe3f00a8dbe2c814f453`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl
mirror: doc/06_spec/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the canonical Vulkan checker and admits only real device evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps device-only admission in the canonical checker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps ProcessingIR receipt fields owned by the macOS harness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
