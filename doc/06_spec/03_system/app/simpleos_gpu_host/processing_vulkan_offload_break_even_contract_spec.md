# processing_vulkan_offload_break_even_contract_spec

> Purpose: execute the Vulkan ProcessingIR break-even lane against its real

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# processing_vulkan_offload_break_even_contract_spec

Purpose: execute the Vulkan ProcessingIR break-even lane against its real

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: execute the Vulkan ProcessingIR break-even lane against its real
artifacts — the checker's self-test (which rejects synthetic evidence), the
validator over the live physical-device receipt, and the receipt's own live
readback fields. Audience: simpleos_gpu_host maintainers and the GPU offload
policy owners.

## Scenarios

### Vulkan ProcessingIR break-even lane contract

#### the live physical-device receipt passes the native validator

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- validate the real receipt with the native validator
   - Expected: file_exists(RECEIPT) is true
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validate the real receipt with the native validator")
expect(file_exists(RECEIPT)).to_equal(true)  # oracle: evidence consumer must have the live receipt
val (stdout, _stderr, code) = process_run("/bin/sh", [CHECKER, "--validate", RECEIPT])
expect(code).to_equal(0)  # oracle: the live receipt validates
expect(stdout).to_contain("processing_ir_vulkan_validation=pass")
```

</details>

#### the checker self-test passes and rejects synthetic evidence

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- run the checker self-test; it must pass, proving the validator fails closed on forged receipts
   - Expected: file_exists(CHECKER) is true
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run the checker self-test; it must pass, proving the validator fails closed on forged receipts")
expect(file_exists(CHECKER)).to_equal(true)
# The gate's self-test rewrites its RAW_SAMPLES in place; point that at
# the self-test scratch dir so live evidence is never clobbered
# (gate bug recorded in doc/08_tracking/bug/sspec_modernization_batch_preexisting_red_specs_2026-08-26.md).
val (stdout, _stderr, code) = process_run("/bin/sh",
    ["-c", "RAW_SAMPLES=build/simpleos_gpu_host/vulkan_break_even/self-test/raw-samples.tsv sh " + CHECKER + " --self-test"])
expect(code).to_equal(0)  # oracle: self-test must exit green
expect(stdout).to_contain("processing_ir_vulkan_self_test=pass")
```

</details>

#### the receipt proves a physical device, exact device readback, no CPU fallback

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- read the receipt fields: live evidence, admitted physical device, exact readback
   - Expected: value_of(receipt, "processing_ir_vulkan_offload_status") equals `pass`
   - Expected: value_of(receipt, "processing_ir_vulkan_offload_evidence_kind") equals `live`
   - Expected: value_of(receipt, "processing_ir_vulkan_offload_physical_device_admitted") equals `true`
   - Expected: value_of(receipt, "processing_ir_vulkan_offload_software_fallback") equals `false`
   - Expected: value_of(receipt, "processing_ir_vulkan_offload_readback_source") equals `device_readback`
   - Expected: value_of(receipt, "processing_ir_vulkan_offload_readback_exact") equals `true`
   - Expected: value_of(receipt, "processing_ir_vulkan_offload_cpu_fallback") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read the receipt fields: live evidence, admitted physical device, exact readback")
val receipt = file_read(RECEIPT)
expect(value_of(receipt, "processing_ir_vulkan_offload_status")).to_equal("pass")
expect(value_of(receipt, "processing_ir_vulkan_offload_evidence_kind")).to_equal("live")  # oracle: synthetic receipts are rejected upstream
expect(value_of(receipt, "processing_ir_vulkan_offload_physical_device_admitted")).to_equal("true")  # oracle: a real physical GPU ran the workload
expect(value_of(receipt, "processing_ir_vulkan_offload_software_fallback")).to_equal("false")  # oracle: no CPU/software-device stand-in
expect(value_of(receipt, "processing_ir_vulkan_offload_readback_source")).to_equal("device_readback")  # oracle: numbers came off the device
expect(value_of(receipt, "processing_ir_vulkan_offload_readback_exact")).to_equal("true")  # oracle: readback bytes matched exactly
expect(value_of(receipt, "processing_ir_vulkan_offload_cpu_fallback")).to_equal("false")
```

</details>

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

- Canonical SPipe generation for source `849cef931935116e9e93cd746a7d43680148ea7b02d45bdb48d17193ab8fef92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `849cef931935116e9e93cd746a7d43680148ea7b02d45bdb48d17193ab8fef92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `849cef931935116e9e93cd746a7d43680148ea7b02d45bdb48d17193ab8fef92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
