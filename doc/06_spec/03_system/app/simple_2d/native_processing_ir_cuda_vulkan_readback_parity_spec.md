# Native Processing Ir Cuda Vulkan Readback Parity Specification

> Tests covering native ProcessingIR CUDA and Vulkan readback parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Processing Ir Cuda Vulkan Readback Parity Specification

## Scenarios

### native ProcessingIR CUDA and Vulkan readback parity

#### uses canonical device-backed readback gates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses canonical device-backed readback gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses canonical device-backed readback gates")
val cuda_source = file_read(CUDA_CHECK)
val vulkan_source = file_read(VULKAN_CHECK)
val processing_source = file_read(PROCESSING_PARITY_CHECK)
expect(cuda_source).to_contain("cuLaunchKernel")
expect(cuda_source).to_contain("cuMemcpyDtoH")
expect(cuda_source).to_contain("cuda_generated_2d_readback_backend_name=cuda")
expect(vulkan_source).to_contain("read_pixels_with_source()")
expect(vulkan_source).to_contain("not-device-readback")
expect(vulkan_source).to_contain("backend-handle-missing")
expect(vulkan_source).to_contain("device-identity-missing")
expect(processing_source).to_contain("set -eu")
expect(processing_source).to_contain("PROCESSING_CUDA_FILL_PROBE_BIN=\"$CUDA_PROBE_BIN\"")
expect(processing_source).to_contain("PROCESSING_CUDA_FILL_TIMEOUT_SECONDS=\"$TIMEOUT_SECONDS\"")
expect(processing_source).to_contain("PROCESSING_CUDA_FILL_MODE=parity")
expect(processing_source).to_contain("PROCESSING_VULKAN_FAULT_PROBE_BIN=\"$VULKAN_PROBE_BIN\"")
expect(processing_source).to_contain("PROCESSING_VULKAN_FAULT_TIMEOUT_SECONDS=\"$TIMEOUT_SECONDS\"")
expect(processing_source).to_contain("check-processing-cuda-fill-native.shs")
expect(processing_source).to_contain("check-processing-vulkan-fault-native.shs")
expect(processing_source).to_contain("processing_cuda_vulkan_native_parity_status=pass")
```

</details>

#### requires exact CUDA pixels and checksums when CUDA is available

- requires exact CUDA pixels and checksums when CUDA is available
   - Expected: file_exists(CUDA_RECEIPT) is true
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires exact CUDA pixels and checksums when CUDA is available")
if not is_linux():
    pending("CUDA native readback is gated to the Linux CUDA host")
else:
    val (_stdout, _stderr, code) = run_cuda_check()
    if not file_exists(CUDA_RECEIPT):
        expect(file_exists(CUDA_RECEIPT)).to_equal(true)
    else:
        val receipt = file_read(CUDA_RECEIPT)
        expect(code).to_equal(0)
        assert_cuda_receipt(receipt)
```

</details>

#### requires exact Vulkan pixels and checksums when Vulkan is available

- requires exact Vulkan pixels and checksums when Vulkan is available
   - Expected: file_exists("bin/simple") is true
   - Expected: code equals `0`
   - Expected: file_exists(VULKAN_RECEIPT) is true
   - Expected: receipt_value(receipt, "vulkan_engine2d_readback_status") equals `pass`
   - Expected: receipt_value(receipt, "vulkan_engine2d_readback_backend_name") equals `vulkan`
   - Expected: receipt_value(receipt, "vulkan_engine2d_readback_present_exercised") equals `true`
   - Expected: receipt_value(receipt, "vulkan_engine2d_readback_readback_exercised") equals `true`
   - Expected: receipt does not contain `cpu_fallback`
   - Expected: receipt does not contain `backend_name=cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires exact Vulkan pixels and checksums when Vulkan is available")
if not is_linux():
    pending("Vulkan Engine2D readback is gated to the Linux Vulkan host")
elif not file_exists("bin/simple"):
    expect(file_exists("bin/simple")).to_equal(true)
else:
    val (stdout, _stderr, code) = run_vulkan_check()
    val evidence_log = if file_exists(VULKAN_LOG): file_read(VULKAN_LOG) else: stdout
    if evidence_log.contains("vulkan_available=false"):
        pending("Vulkan device unavailable; canonical receipt records an honest host gate")
    else:
        expect(code).to_equal(0)
        expect(file_exists(VULKAN_RECEIPT)).to_equal(true)
        val receipt = file_read(VULKAN_RECEIPT)
        expect(receipt_value(receipt, "vulkan_engine2d_readback_status")).to_equal("pass")
        expect(receipt_value(receipt, "vulkan_engine2d_readback_backend_name")).to_equal("vulkan")
        expect(receipt_value(receipt, "vulkan_engine2d_readback_present_exercised")).to_equal("true")
        expect(receipt_value(receipt, "vulkan_engine2d_readback_readback_exercised")).to_equal("true")
        expect(receipt.contains("cpu_fallback")).to_equal(false)
        expect(receipt.contains("backend_name=cpu")).to_equal(false)
        assert_vulkan_operation(receipt, "clear")
        assert_vulkan_operation(receipt, "rect")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native ProcessingIR CUDA and Vulkan readback parity.
- native ProcessingIR CUDA and Vulkan readback parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `373fbf0718711e92f6446d290ab9c86fcc8554f9d956b9966d5af4caa1d25f22`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `373fbf0718711e92f6446d290ab9c86fcc8554f9d956b9966d5af4caa1d25f22`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `373fbf0718711e92f6446d290ab9c86fcc8554f9d956b9966d5af4caa1d25f22`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses canonical device-backed readback gates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires exact CUDA pixels and checksums when CUDA is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/native_processing_ir_cuda_vulkan_readback_parity_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires exact Vulkan pixels and checksums when Vulkan is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
