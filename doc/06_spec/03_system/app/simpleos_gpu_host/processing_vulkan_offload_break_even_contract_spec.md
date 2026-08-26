# Processing Vulkan Offload Break Even Contract Specification

> Tests covering Vulkan ProcessingIR break-even lane contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing Vulkan Offload Break Even Contract Specification

## Scenarios

### Vulkan ProcessingIR break-even lane contract

#### uses a real physical Vulkan device and exact staged readback

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses a real physical Vulkan device and exact staged readback
   - Expected: file_exists(PRODUCER) is true
   - Expected: source does not contain `CmdFillBuffer`
   - Expected: source does not contain `vkCmdFillBuffer`
   - Expected: source does not contain `cuda`
   - Expected: source does not contain `c_cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses a real physical Vulkan device and exact staged readback")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(file_exists(PRODUCER)).to_equal(true)
val source = file_read(PRODUCER)
for marker in [
    "#include <vulkan/vulkan.h>", "dlopen(\"libvulkan.so.1\"",
    "VK_PHYSICAL_DEVICE_TYPE_CPU", "VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU",
    "VK_PHYSICAL_DEVICE_TYPE_INTEGRATED_GPU", "VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT",
    "VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT", "VK_MEMORY_PROPERTY_HOST_CACHED_BIT",
    "physical_device_admitted=true", "cpu_fallback=false",
    "readback_source=device_readback", "readback_exact=true",
    "copy_buffer", "CmdDispatch", "dispatch", "FILL_REPETITIONS",
    "VK_BUFFER_USAGE_STORAGE_BUFFER_BIT", "VkShaderModule",
    "VkDescriptorSetLayout", "VkDescriptorPool", "VkDescriptorSet",
    "VkPipelineLayout", "VkPipeline", "VkBufferMemoryBarrier",
    "VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT", "VK_ACCESS_SHADER_WRITE_BIT",
    "VK_WHOLE_SIZE", "fill_spirv"
]:
    expect(source).to_contain(marker)
expect(source.contains("CmdFillBuffer")).to_equal(false)
expect(source.contains("vkCmdFillBuffer")).to_equal(false)
expect(source.contains("cuda")).to_equal(false)
expect(source.contains("c_cuda")).to_equal(false)
```

</details>

#### keeps CPU and GPU work, sample counts, and both command modes bound

- keeps CPU and GPU work, sample counts, and both command modes bound


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps CPU and GPU work, sample counts, and both command modes bound")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = file_read(PRODUCER)
val checker = file_read(CHECKER)
expect(source).to_contain("dispatch_fill_u32_repeated_v1")
expect(source).to_contain("cpu_fill")
expect(source).to_contain("FILL_REPETITIONS")
expect(source).to_contain("parse_int(argv[3],3,64")
expect(source).to_contain("parse_int(argv[4],5,64")
expect(source).to_contain("COMMANDS_PER_ROW")
expect(source).to_contain("batched")
expect(source).to_contain("per_command")
expect(source).to_contain("mismatch")
expect(checker).to_contain("WARMUPS=")
expect(checker).to_contain("SAMPLES=")
expect(checker).to_contain("raw-samples.tsv")
expect(checker).to_contain("raw_ids")
expect(checker).to_contain("raw_ids \"$RAW_SAMPLES\" \"$b\" \"$mode\" || return 1")
expect(checker).to_contain("raw_median \"$RAW_SAMPLES\" \"$b\" \"$mode\" 8")
expect(checker).to_contain("first_fast_communication=$((up + down))")
expect(checker).to_contain("processing_ir_vulkan_offload_communication_overhead_us")
expect(checker).to_contain("dispatch_count")
expect(checker).to_contain("workgroup_count")
expect(checker).to_contain("spirv-val")
expect(checker).to_contain("--dump-spirv")
expect(checker).to_contain("producer_source_sha256")
expect(checker).to_contain("producer_artifact_sha256")
expect(checker).to_contain("--self-test")
expect(checker).to_contain("--validate")
expect(checker).to_contain("device_readback")
expect(checker).to_contain("cpu_fallback")
```

</details>

#### does not admit synthetic evidence as live Vulkan evidence

- does not admit synthetic evidence as live Vulkan evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not admit synthetic evidence as live Vulkan evidence")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val checker = file_read(CHECKER)
expect(checker).to_contain("EXPECTED_EVIDENCE_KIND=live")
expect(checker).to_contain("EXPECTED_EVIDENCE_KIND=validator-self-test")
expect(checker).to_contain("if validate_receipt; then return 1; fi")
expect(checker).to_contain("processing_ir_vulkan_offload_physical_device_admitted")
expect(checker).to_contain("processing_ir_vulkan_offload_software_fallback")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan ProcessingIR break-even lane contract.
- Vulkan ProcessingIR break-even lane contract

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

- Canonical SPipe generation for source `44a3c7bb76c74a1b1079c3d210c9aded41817dbf36cd42718926b6968ee5ec04`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `44a3c7bb76c74a1b1079c3d210c9aded41817dbf36cd42718926b6968ee5ec04`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `44a3c7bb76c74a1b1079c3d210c9aded41817dbf36cd42718926b6968ee5ec04`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/processing_vulkan_offload_break_even_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
